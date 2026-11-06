"""T8: can an agent that has only the reference write verified programs with the features of 0.3, and
what does `i32` cost it? Three tasks exist twice, the same but for `i32` and `int`. See bench/runs/t8-features.

    python -m verifbench.features --run bench/runs/t8-features --trials 3
    python -m verifbench.features --selfcheck DIR    # DIR/<task>/*.quod: reference solutions
    python -m verifbench.features --hidden TASK DIR  # DIR holds the generated Python
"""
from __future__ import annotations

import argparse
import concurrent.futures as futures
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any, Callable

PROMPT = """\
Implement what is below in Quod, in the file `solution.quod` in the current directory{extra_file}.

Quod is a new verified programming language. Its tools are available to you as MCP tools:
`quod_reference` (the language reference: it is all there is to know about Quod), `quod_check`,
`quod_run` and `quod_build`. There is no shell.

## Specification
{spec}

## Required declarations (add the contracts yourself; helper functions are allowed)
```rust
{sig}
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod_check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- `solution.quod` must pass `quod_check` (call it with `path: "solution.quod"`).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
"""


class T:
    def __init__(self, id: str, spec: str, sig: str, test: Callable[[Any, random.Random], list[bool]], feature: str, pair: str | None = None, extra: str = ""):
        self.id, self.spec, self.sig, self.test, self.feature, self.pair, self.extra = id, spec, sig, test, feature, pair, extra


def is_case(v: Any, case: str) -> bool:
    return type(v).__name__ == case or type(v).__name__.endswith("_" + case)


# --- discount ---------------------------------------------------------------
DISCOUNT_SPEC = """A price after a discount, in cents. A `Regular` customer gets no discount, a `Member` 5%, or 10% from
5 years of membership on (the field is the number of years), `Staff` 30%. The discount is rounded down: the result is
`amount - amount * percent / 100`. The input guarantees `0 <= amount <= 10000000`."""
DISCOUNT_SIG = "enum Customer { Regular, Member(nat), Staff }\n\nfn discounted(amount: {t}, c: Customer) -> {t}"


def t_discount(s, r):
    out = []
    for a in [0, 1, 19, 99, 100, 101, 10000000, 9999999] + [r.randint(0, 10000000) for _ in range(40)]:
        out.append(s.discounted(a, s.Regular()) == a)
        out.append(s.discounted(a, s.Staff()) == a - a * 30 // 100)
        for y in (0, 4, 5, 6):
            out.append(s.discounted(a, s.Member(y)) == a - a * (10 if y >= 5 else 5) // 100)
    return out


# --- total ------------------------------------------------------------------
TOTAL_SPEC = """The sum of the elements of `xs`, 0 if it is empty. The input guarantees `len(xs) <= 1000000`."""


def t_total(bound):
    def test(s, r):
        out = [s.total([]) == 0, s.total([5]) == 5, s.total([bound, bound, bound]) == 3 * bound, s.total([-bound - 1, -bound - 1]) == 2 * (-bound - 1)]
        for _ in range(40):
            xs = [r.randint(-bound - 1, bound) for _ in range(r.randint(0, 30))]
            out.append(s.total(xs) == sum(xs))
        return out
    return test


# --- clamp_add --------------------------------------------------------------
CLAMP_SPEC = """`a + b`, brought back into the range from `lo` to `hi` included: `lo` if the sum is below it, `hi` if it is above it.
The input guarantees `lo <= hi`."""


def t_clamp(bound):
    def test(s, r):
        lo32, hi32 = -2**31, 2**31 - 1
        out = [s.clamp_add(hi32, hi32, 0, 10) == 10, s.clamp_add(lo32, lo32, -5, 5) == -5, s.clamp_add(1, 2, 0, 10) == 3, s.clamp_add(hi32, 1, lo32, hi32) == hi32, s.clamp_add(lo32, -1, lo32, hi32) == lo32]
        for _ in range(60):
            lo = r.randint(lo32, hi32)
            hi = r.randint(lo, hi32)
            a, b = r.randint(lo32, hi32), r.randint(lo32, hi32)
            out.append(s.clamp_add(a, b, lo, hi) == min(max(a + b, lo), hi))
        return out
    return test


# --- invoice_total ----------------------------------------------------------
def t_invoice(s, r):
    out = [s.invoice_total([]) == 0, s.invoice_total([s.Line(2**31 - 1, 2**31 - 1), s.Line(2**31 - 1, 2**31 - 1)]) == 2 * (2**31 - 1) ** 2]
    for _ in range(40):
        ls = [(r.randint(-1000, 1000), r.randint(-100000, 100000)) for _ in range(r.randint(0, 20))]
        out.append(s.invoice_total([s.Line(q, u) for q, u in ls]) == sum(q * u for q, u in ls))
    return out


# --- parse_kv ---------------------------------------------------------------
def t_parse(s, r):
    def want(x):
        if "=" not in x:
            return None
        k, v = x.split("=", 1)
        ws = " \t\n\r"
        k, v = k.strip(ws), v.strip(ws)
        return None if k == "" else (k, v)
    cases = ["", "=", "a", "a=b", " a = b ", "a=", "=b", "  =b", "a=b=c", " key =  a value  ", "\ta\t=\tb\t", "é=ü", "a b=c d", "==", "x= =y"]
    out = []
    for c in cases:
        g, w = s.parse_kv(c), want(c)
        out.append(is_case(g, "None") if w is None else (is_case(g, "Some") and tuple(g.f0) == w))
    return out


# --- first_index ------------------------------------------------------------
def t_first(s, r):
    out = []
    cases = [([], 1), ([1], 1), ([1], 2), ([2, 1, 1], 1), ([1, 1], 1), ([-2**31, 2**31 - 1], 2**31 - 1)]
    for _ in range(40):
        cases.append(([r.randint(0, 5) for _ in range(r.randint(0, 12))], r.randint(0, 5)))
    for xs, x in cases:
        g = s.first_index(xs, x)
        out.append(is_case(g, "Some") and g.f0 == xs.index(x) if x in xs else is_case(g, "None"))
    return out


# --- step -------------------------------------------------------------------
def t_step(s, r):
    states = [s.Draft(), s.Paid(5), s.Shipped("t"), s.Cancelled()]
    events = [s.Pay(7), s.Pay(0), s.Pay(-1), s.Ship("x"), s.Ship(""), s.Cancel()]

    def want(a, e):
        if is_case(a, "Draft") and is_case(e, "Pay"):
            return ("ok", s.Paid(e.f0)) if e.f0 > 0 else ("err", "bad amount")
        if is_case(a, "Paid") and is_case(e, "Ship"):
            return ("ok", s.Shipped(e.f0)) if e.f0 != "" else ("err", "no tracking")
        if (is_case(a, "Draft") or is_case(a, "Paid")) and is_case(e, "Cancel"):
            return ("ok", s.Cancelled())
        return ("err", "invalid")
    out = []
    for a in states:
        for e in events:
            g, (k, v) = s.step(a, e), want(a, e)
            out.append(is_case(g, "Ok" if k == "ok" else "Err") and g.f0 == v)
    return out


# --- generic ----------------------------------------------------------------
def t_generic(s, r):
    return [s.last_score([]) == 0, s.last_score([3]) == 3, s.last_score([1, -2]) == -2, s.last_flag([]) is False, s.last_flag([True]) is True, s.last_flag([True, False]) is False]


# --- modules ----------------------------------------------------------------
def t_module(s, r):
    import money
    out = []
    bound = 10**15
    for _ in range(30):
        a, b, c = (r.randint(-bound, bound) for _ in range(3))
        out.append(s.total_of(money.Money(a), money.Money(b), money.Money(c)) == money.Money(a + b + c))
    return out


TASKS = [
    T("discount_i32", DISCOUNT_SPEC, DISCOUNT_SIG.replace("{t}", "i32"), t_discount, "enum, match, i32", "discount"),
    T("discount_int", DISCOUNT_SPEC, DISCOUNT_SIG.replace("{t}", "int"), t_discount, "enum, match", "discount"),
    T("total_i32", TOTAL_SPEC, "fn total(xs: seq<i32>) -> i64", t_total(2**31 - 1), "i32, i64, loop", "total"),
    T("total_int", TOTAL_SPEC, "fn total(xs: seq<int>) -> int", t_total(2**31 - 1), "loop", "total"),
    T("clamp_i32", CLAMP_SPEC, "fn clamp_add(a: i32, b: i32, lo: i32, hi: i32) -> i32", t_clamp(2**31 - 1), "i32 overflow", "clamp"),
    T("clamp_int", CLAMP_SPEC, "fn clamp_add(a: int, b: int, lo: int, hi: int) -> int", t_clamp(2**31 - 1), "plain", "clamp"),
    T("invoice_total", "The total of an invoice: the sum, over its lines, of `qty * unit_cents`, 0 if it has no line. Quantities and prices can be negative (a return, a credit).",
      "struct Line { qty: i32, unit_cents: i32 }\n\nfn invoice_total(lines: seq<Line>) -> int", t_invoice, "struct, i32, loop"),
    T("parse_kv", """Parse a `key=value` line. Split `s` at its first `=`. `key` is what is before it and `value` what is after it,
both without the white space at their ends, as `strings.trim` of the standard library removes it. The result is `None` if `s` has no `=`,
or if the key is empty once trimmed, and `Some((key, value))` otherwise. Use the modules `strings` and `option` of the standard library.""",
      "import option\nimport strings\n\nfn parse_kv(s: string) -> option.Option<(string, string)>", t_parse, "string, stdlib, Option"),
    T("first_index", "The index of the first element of `xs` equal to `x`, in an `option.Some`, or `option.None` if there is none. Use the module `option` of the standard library.",
      "import option\n\nfn first_index(xs: seq<i32>, x: i32) -> option.Option<nat>", t_first, "Option, loop, match"),
    T("step", """One step of the life of an order. From `Draft`, `Pay(a)` gives `Paid(a)` if `a > 0`, or else the error `"bad amount"`. From `Paid(a)`,
`Ship(t)` gives `Shipped(t)` if `t` is not empty, or else the error `"no tracking"`. From `Draft` or `Paid`, `Cancel` gives `Cancelled`.
Anything else is the error `"invalid"`. A new state is an `option.Ok`, an error an `option.Err`. Use the module `option` of the standard library.""",
      "import option\n\nenum State { Draft, Paid(i32), Shipped(string), Cancelled }\nenum Event { Pay(i32), Ship(string), Cancel }\n\nfn step(s: State, e: Event) -> option.Result<State, string>", t_step, "enum, nested match, Result"),
    T("generic_last", """`last_or` gives the last element of `xs`, or `other` if `xs` is empty. `last_score` is `last_or` with 0 for `other`, and `last_flag` is `last_or` with `false`. Both must call `last_or`.""",
      "fn last_or<T>(xs: seq<T>, other: T) -> T\nfn last_score(xs: seq<i32>) -> i32\nfn last_flag(xs: seq<bool>) -> bool", t_generic, "generics"),
    T("module_total", """A module `money`, in the file `money.quod` next to `solution.quod`, has the struct `Money` and the function `add`, the sum of two amounts. Its `requires` says what `add` needs not to overflow.
`total_of`, in `solution.quod`, adds three amounts with `money.add`. The input of `total_of` guarantees that each of its amounts is between -1000000000000000 and 1000000000000000.""",
      "// money.quod\nstruct Money { cents: i64 }\nfn add(a: Money, b: Money) -> Money\n\n// solution.quod\nimport money\nfn total_of(a: money.Money, b: money.Money, c: money.Money) -> money.Money", t_module, "modules, struct, i64", extra=" and the file `money.quod` next to it"),
]
BY_ID = {t.id: t for t in TASKS}


def hidden(task: str, directory: Path) -> dict[str, Any]:
    sys.path.insert(0, str(directory))
    try:
        import solution
    except Exception as e:
        return {"loaded": False, "error": repr(e)[:300]}
    try:
        results = BY_ID[task].test(solution, random.Random(20261106))
    except Exception as e:
        return {"loaded": True, "total": None, "passed": None, "error": repr(e)[:300]}
    return {"loaded": True, "total": len(results), "passed": sum(1 for x in results if x)}


def sh(cmd: list[str] | str, cwd: Path, timeout: int, stdin: str | None = None, env: dict[str, str] | None = None) -> dict[str, Any]:
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=cwd, input=stdin, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=timeout, shell=isinstance(cmd, str), env=env)
        return {"code": p.returncode, "out": p.stdout, "err": p.stderr, "secs": round(time.monotonic() - t0, 1)}
    except subprocess.TimeoutExpired:
        return {"code": None, "out": "", "err": "timeout", "secs": timeout}


CSPROJ = '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Library</OutputType><TargetFramework>net472</TargetFramework><LangVersion>7.3</LangVersion><EnableDefaultCompileItems>false</EnableDefaultCompileItems></PropertyGroup><ItemGroup><Compile Include="*.cs" /><Reference Include="System.Numerics" /></ItemGroup></Project>\n'


def evaluate(task: T, work: Path, quod: str) -> dict[str, Any]:
    work = work.resolve()
    res: dict[str, Any] = {"submitted": (work / "solution.quod").exists()}
    if not res["submitted"]:
        return res
    texts = "\n".join(p.read_text(encoding="utf-8", errors="replace") for p in work.glob("*.quod"))
    res["loose"] = len(re.findall(r"\bloose\b", texts))
    res["ensures"] = len(re.findall(r"\bensures\b", texts))
    v = sh([quod, "check", "solution.quod", "--require-contracts"], work, 600)
    res["verified"] = v["code"] == 0
    res["check_tail"] = (v["out"] + v["err"])[-500:]
    build = work / "_py"
    shutil.rmtree(build, ignore_errors=True)
    b = sh([quod, "build", "solution.quod", "-o", str(build), "--require-contracts"], work, 600)
    if b["code"] != 0:
        res["hidden"] = {"loaded": False, "error": "not built: " + (b["out"] + b["err"])[-300:]}
    else:
        h = sh([sys.executable, "-m", "verifbench.features", "--hidden", task.id, str(build)], Path(__file__).resolve().parent.parent, 120)
        try:
            res["hidden"] = json.loads(h["out"].strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError):
            res["hidden"] = {"loaded": False, "error": (h["err"] or h["out"])[-300:]}
    # the C# of what is accepted: does it compile, on .NET Framework and C# 7.3?
    if res["verified"]:
        cs = Path(tempfile.mkdtemp())
        g = sh([quod, "build", "solution.quod", "--target", "csharp", "-o", str(cs), "--require-contracts"], work, 600)
        if g["code"] != 0:
            res["csharp"] = "not generated: " + (g["out"] + g["err"])[-200:]
        else:
            (cs / "p.csproj").write_text(CSPROJ, encoding="utf-8")
            c = sh("dotnet build -c Release -v q -nologo", cs, 300)
            errors = sorted(set(re.findall(r"error (CS\d+)", c["out"])))
            res["csharp"] = "ok" if c["code"] == 0 else "does not compile: " + ", ".join(errors)
        shutil.rmtree(cs, ignore_errors=True)
    h = res.get("hidden") or {}
    res["all_pass"] = bool(h.get("loaded")) and h.get("total") is not None and h.get("passed") == h.get("total")
    return res


def parse_events(stdout: str) -> dict[str, Any]:
    """What the agent did, from `--output-format stream-json`. A tool answers in JSON, its structured result."""
    names: dict[str, str] = {}
    calls: dict[str, int] = {}
    m: dict[str, Any] = {"check_rejected": 0, "proof_failures": 0, "fits_failures": 0, "type_errors": 0, "underspecified": 0, "style_rejected": 0}
    errors: list[str] = []
    for line in stdout.splitlines():
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(e, dict):  # the stream can hold a line of plain JSON text
            continue
        if e.get("type") == "result":
            usage = e.get("usage") or {}
            m.update(turns=e.get("num_turns"), cost_usd=e.get("total_cost_usd"), agent_error=e.get("is_error"), result_text=str(e.get("result"))[:300],
                     out_tokens=usage.get("output_tokens"), duration_secs=round((e.get("duration_ms") or 0) / 1000, 1))
            continue
        message = e.get("message")  # a string in some system events
        content = message.get("content") if isinstance(message, dict) else None
        for c in content if isinstance(content, list) else []:
            if not isinstance(c, dict):
                continue
            if c.get("type") == "tool_use":
                names[c["id"]] = c["name"]
                short = c["name"].replace("mcp__quod__", "")
                calls[short] = calls.get(short, 0) + 1
            elif c.get("type") == "tool_result" and names.get(c.get("tool_use_id"), "").endswith("quod_check"):
                body = c.get("content")
                text = body if isinstance(body, str) else " ".join(x.get("text", "") if isinstance(x, dict) else str(x) for x in body or [])
                try:
                    j = json.loads(text)
                except json.JSONDecodeError:
                    continue
                if not isinstance(j, dict) or j.get("verified", True):
                    continue
                m["check_rejected"] += 1
                for d in j.get("diagnostics") or []:
                    if d.get("severity") != "error":
                        continue
                    kind = d.get("kind")
                    errors.append(f"{kind}/{d.get('status')}: {str(d.get('property') or d.get('message'))[:90]}")
                    if kind == "proof":
                        m["proof_failures"] += 1
                        m["fits_failures"] += 1 if "fits in" in str(d.get("property")) else 0
                    elif kind == "completeness":
                        m["underspecified"] += 1
                    elif kind == "contract":
                        m["style_rejected"] += 1
                    else:
                        m["type_errors"] += 1
    m["calls"] = calls
    m["errors"] = errors
    return m


def one(task: T, trial: int, out: Path, quod: str, model: str, lock: threading.Lock, stop: threading.Event) -> None:
    if stop.is_set():
        return
    work = out / "work" / f"{task.id}__{trial}"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    config = work / ".mcp.json"
    config.write_text(json.dumps({"mcpServers": {"quod": {"command": quod, "args": ["mcp", "--require-contracts"]}}}), encoding="utf-8")
    tools = "Read,Write,Edit,Glob,Grep," + ",".join("mcp__quod__" + t for t in ("quod_check", "quod_run", "quod_build", "quod_reference"))
    cmd = f'claude -p --output-format stream-json --verbose --model {model} --permission-mode acceptEdits --mcp-config ".mcp.json" --strict-mcp-config --allowedTools "{tools}"'
    prompt = PROMPT.format(spec=task.spec, sig=task.sig, extra_file=task.extra)
    r = sh(cmd, work, 1200, stdin=prompt)
    (work / "agent_stdout.jsonl").write_text(r["out"], encoding="utf-8")
    (work / "agent_stderr.txt").write_text(r["err"], encoding="utf-8")
    m = parse_events(r["out"])
    text = (m.get("result_text") or "").lower()
    limit = bool(m.get("agent_error")) and any(w in text for w in ("usage limit", "rate limit", "limit reached", "429", "quota"))
    row = {"task": task.id, "feature": task.feature, "pair": task.pair, "trial": trial, "model": model, "secs": r["secs"], "exit": r["code"], "limit": limit, **m, **evaluate(task, work, quod)}
    with lock:
        with open(out / "results.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
        print(task.id, trial, "verified", row.get("verified"), "pass", row.get("all_pass"), "cs", row.get("csharp"), "secs", r["secs"], "checks", m["calls"].get("quod_check"), "cost", m.get("cost_usd"), flush=True)
    if limit:
        stop.set()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--run", type=Path)
    p.add_argument("--trials", type=int, default=3)
    p.add_argument("--workers", type=int, default=3)
    p.add_argument("--model", default="claude-haiku-5-5")
    p.add_argument("--quod", default=None)
    p.add_argument("--tasks", default="all")
    p.add_argument("--selfcheck", type=Path)
    p.add_argument("--hidden", nargs=2)
    p.add_argument("--reparse", type=Path, help="recompute what the agents did from their saved transcripts")
    a = p.parse_args()
    if a.hidden:
        print(json.dumps(hidden(a.hidden[0], Path(a.hidden[1]))))
        return
    if a.reparse:
        rows = [json.loads(line) for line in (a.reparse / "results.jsonl").read_text(encoding="utf-8").splitlines()]
        for row in rows:
            for k in ("cannot_prove",):
                row.pop(k, None)
            text = (a.reparse / "work" / f"{row['task']}__{row['trial']}" / "agent_stdout.jsonl").read_text(encoding="utf-8")
            row.update(parse_events(text))
        (a.reparse / "results.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows), encoding="utf-8")
        return
    quod = a.quod or str(Path(__file__).resolve().parents[2] / "artifacts" / "aot-0.3.0" / "quod.exe")
    if a.selfcheck:
        for t in TASKS:
            d = a.selfcheck / t.id
            if d.exists():
                r = evaluate(t, d, quod)
                print(t.id, "verified", r.get("verified"), "hidden", r.get("hidden"), "cs", r.get("csharp"), "loose", r.get("loose"))
                if not r.get("verified"):
                    print("   ", r.get("check_tail", "")[-400:].replace("\n", "\n    "))
            else:
                print(t.id, "no reference")
        return
    a.run.mkdir(parents=True, exist_ok=True)
    done = set()
    if (a.run / "results.jsonl").exists():
        for line in (a.run / "results.jsonl").read_text(encoding="utf-8").splitlines():
            row = json.loads(line)
            if not row.get("limit"):
                done.add((row["task"], row["trial"]))
    chosen = TASKS if a.tasks == "all" else [BY_ID[x] for x in a.tasks.split(",")]
    jobs = [(t, k) for k in range(a.trials) for t in chosen if (t.id, k) not in done]
    lock, stop = threading.Lock(), threading.Event()
    with futures.ThreadPoolExecutor(a.workers) as pool:
        for f in futures.as_completed([pool.submit(one, t, k, a.run, quod, a.model, lock, stop) for t, k in jobs]):
            f.result()
    print("stopped on a usage limit" if stop.is_set() else "done")


if __name__ == "__main__":
    main()
