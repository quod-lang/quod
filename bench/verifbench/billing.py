"""T9: an agent on a program of real size. A billing engine over three modules, from invented rules (the VAT rates are
the public French ones). Scored by a Python oracle written apart from any Quod, on the Python and on the C# generated,
and by a client that proves properties from the contracts alone. See bench/runs/t9-billing.

    python -m verifbench.billing --run bench/runs/t9-billing --models claude-haiku-5-5,claude-sonnet-5-5 --trials 3
    python -m verifbench.billing --selfcheck DIR    # DIR/{catalog,discounts,solution}.quod: a reference solution
"""
from __future__ import annotations

import argparse
import concurrent.futures as futures
import json
import random
import re
import shutil
import sys
import tempfile
import threading
from pathlib import Path
from typing import Any

from verifbench.features import parse_events, sh

SPEC = """\
# A billing engine

All amounts are in cents, and every division rounds down unless said otherwise. The order of the rules matters.

## Validation
`price` answers `option.Err(message)` with the first of these that applies:
1. `"empty order"`: the order has no line.
2. `"too many lines"`: it has more than 1000 lines.
3. `"bad line"`: a line has `qty` outside 1..10000, `unit_cents` outside 0..100000000, or `grams` outside 0..1000000 (all included).
4. `"bad customer"`: a `Member` with a negative number of years.
5. `"bad coupon"`: a `Percent` outside 0..50 (included), or a negative `Fixed`.

Otherwise it answers `option.Ok(invoice)`, with the following.

## One line
- `gross` is `qty * unit_cents`.
- Volume discount: 10% from a quantity of 100, 5% from 10, otherwise none. `Book` lines never get one.
- The net of a line is `gross - gross * percent / 100`.

## The order
- `subtotal` is the sum of the nets of the lines.
- Customer discount, on the subtotal: `Guest` none. `Member(years)` 5% from 5 years, otherwise 2%. `Business` 3% if the subtotal is at least 100000, otherwise none. That is `subtotal * percent / 100`.
- Coupon discount, on `subtotal - customer discount`: `Percent(p)` is `amount * p / 100`, `Fixed(v)` is the smaller of `v` and the amount, the others none.
- `discount` is the sum of both, but at most `subtotal * 30 / 100`.
- `net` is `subtotal - discount`.

## Shipping
- With a coupon `FreeShipping`, or when `net` reaches the threshold of free shipping, `shipping` is 0. That threshold is 5000 for a `Member`, 10000 for anyone else.
- Otherwise it depends on the total weight `g`, the sum over the lines of `qty * grams`: 0 if `g` is 0; 490 up to 1000 grams included; 690 up to 5000 included; above that, `990 + 100 * ((g - 5000 + 999) / 1000)`.

## VAT
- The rates are 20% for `Standard`, 5.5% for `Food` and `Book`, 2.1% for `Medicine`: 200, 55, 55 and 21 per thousand.
- The `discount` of the order is taken from the nets of the categories, first from all of `Standard`, what remains of it from `Food`, then `Book`, then `Medicine`. Each takes as much as it can, up to its own net. What is left of each category is its base.
- The VAT of a base is `(base * rate + 500) / 1000`. The VAT of the shipping is the same at 200 per thousand.
- `vat` is the sum of the VAT of the four bases and of the shipping.
- **Reverse charge:** `vat` is 0 for a `Business` whose VAT number is not empty, when `country` is not `"FR"`.

## The invoice
`total` is `net + shipping + vat`.

## What the contract of `price` must let others rely on
`price` must be a function whose contract determines its result, and from which a caller can prove, with nothing but this contract:
- an empty order gives `option.Err("empty order")`;
- on `option.Ok(i)`: `i.total == i.net + i.shipping + i.vat`, and `i.net == i.subtotal - i.discount`;
- on `option.Ok(i)`: `i.discount >= 0` and `i.discount <= i.subtotal * 30 / 100`;
- on `option.Ok(i)`: `i.total >= 0`.
"""

SIG = """\
// catalog.quod
enum Category { Standard, Food, Book, Medicine }
struct Line { sku: string, category: Category, qty: {q}, unit_cents: {q}, grams: {q} }

// discounts.quod
enum Customer { Guest, Member({q}), Business(string) }
enum Coupon { NoCoupon, Percent({q}), Fixed({q}), FreeShipping }

// solution.quod
import catalog
import discounts
import option

struct Order { lines: seq<catalog.Line>, customer: discounts.Customer, coupon: discounts.Coupon, country: string }
struct Invoice { subtotal: {a}, discount: {a}, net: {a}, shipping: {a}, vat: {a}, total: {a} }

fn price(o: Order) -> option.Result<Invoice, string>
"""

PROMPT = """\
Implement the program below in Quod, in the files `catalog.quod`, `discounts.quod` and `solution.quod` in the current directory.

Quod is a new verified programming language. Its tools are available to you as MCP tools:
`quod_reference` (the language reference: it is all there is to know about Quod), `quod_check`,
`quod_run` and `quod_build`. There is no shell.

{spec}

## Required declarations (add the contracts yourself; helper functions, lemmas and modules' private functions are allowed)
```rust
{sig}
```

## Rules
- `quod_check` rejects a contract that accepts two different results for the same input. Add invariants, `decreases`, lemmas and helpers as needed.
- `solution.quod` must pass `quod_check` (call it with `path: "solution.quod"`). It checks the modules it imports too.
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python and to C#, and evaluated against hidden tests.
"""

# What a caller can prove from the contract of `price` alone: one function per property of the specification.
CLIENT = """\
import catalog
import discounts
import option
import solution

fn p_empty(c: discounts.Customer, k: discounts.Coupon, s: string) -> bool
  ensures result
{
  let r = solution.price(solution.Order([], c, k, s));
  assert r == option.Err("empty order");
  true
}

fn p_sums(o: solution.Order) -> bool
  ensures result
{
  let r = solution.price(o);
  assert match r { Ok(i) => i.total == i.net + i.shipping + i.vat && i.net == i.subtotal - i.discount, Err(_) => true };
  true
}

fn p_cap(o: solution.Order) -> bool
  ensures result
{
  let r = solution.price(o);
  assert match r { Ok(i) => i.discount >= 0 && i.discount <= i.subtotal * 30 / 100, Err(_) => true };
  true
}

fn p_positive(o: solution.Order) -> bool
  ensures result
{
  let r = solution.price(o);
  assert match r { Ok(i) => i.total >= 0, Err(_) => true };
  true
}
"""
PROPERTIES = ["p_empty", "p_sums", "p_cap", "p_positive"]

CATEGORIES = ["Standard", "Food", "Book", "Medicine"]
RATES = {"Standard": 200, "Food": 55, "Book": 55, "Medicine": 21}


def oracle(o: dict[str, Any]) -> tuple:
    """The rules, written from the specification with no Quod at hand. `o` is plain data."""
    lines, cu, co = o["lines"], o["customer"], o["coupon"]
    if not lines:
        return ("err", "empty order")
    if len(lines) > 1000:
        return ("err", "too many lines")
    for li in lines:
        if not (1 <= li["qty"] <= 10000 and 0 <= li["unit"] <= 100000000 and 0 <= li["grams"] <= 1000000):
            return ("err", "bad line")
    if cu[0] == "Member" and cu[1] < 0:
        return ("err", "bad customer")
    if (co[0] == "Percent" and not 0 <= co[1] <= 50) or (co[0] == "Fixed" and co[1] < 0):
        return ("err", "bad coupon")
    nets = {c: 0 for c in CATEGORIES}
    grams = 0
    for li in lines:
        gross = li["qty"] * li["unit"]
        pct = 0 if li["cat"] == "Book" else 10 if li["qty"] >= 100 else 5 if li["qty"] >= 10 else 0
        nets[li["cat"]] += gross - gross * pct // 100
        grams += li["qty"] * li["grams"]
    subtotal = sum(nets.values())
    if cu[0] == "Member":
        cd = subtotal * (5 if cu[1] >= 5 else 2) // 100
    elif cu[0] == "Business" and subtotal >= 100000:
        cd = subtotal * 3 // 100
    else:
        cd = 0
    amount = subtotal - cd
    kd = amount * co[1] // 100 if co[0] == "Percent" else min(co[1], amount) if co[0] == "Fixed" else 0
    discount = min(cd + kd, subtotal * 30 // 100)
    net = subtotal - discount
    if co[0] == "FreeShipping" or net >= (5000 if cu[0] == "Member" else 10000):
        ship = 0
    elif grams == 0:
        ship = 0
    elif grams <= 1000:
        ship = 490
    elif grams <= 5000:
        ship = 690
    else:
        ship = 990 + 100 * ((grams - 5000 + 999) // 1000)
    if cu[0] == "Business" and cu[1] != "" and o["country"] != "FR":
        vat = 0
    else:
        rest, vat = discount, 0
        for c in CATEGORIES:
            taken = min(rest, nets[c])
            rest -= taken
            vat += ((nets[c] - taken) * RATES[c] + 500) // 1000
        vat += (ship * 200 + 500) // 1000
    return ("ok", subtotal, discount, net, ship, vat, net + ship + vat)


def cases(seed: int, n: int) -> list[dict[str, Any]]:
    r = random.Random(seed)

    def line(bad: bool = False):
        qty = r.choice([1, 2, 9, 10, 11, 99, 100, 101, 10000, r.randint(1, 500)])
        unit = r.choice([0, 1, 99, 100, 199, 2500, 100000000, r.randint(0, 100000)])
        grams = r.choice([0, 1, 100, 999, 1000, 5000, 1000000, r.randint(0, 3000)])
        li = {"sku": "s" + str(r.randint(0, 9)), "cat": r.choice(CATEGORIES), "qty": qty, "unit": unit, "grams": grams}
        if bad:
            k, v = r.choice([("qty", 0), ("qty", -1), ("qty", 10001), ("unit", -1), ("unit", 100000001), ("grams", -1), ("grams", 1000001)])
            li[k] = v
        return li

    def customer():
        return r.choice([("Guest",), ("Member", r.choice([0, 4, 5, 6, 30])), ("Business", r.choice(["", "FR123", "DE99"]))])

    def coupon():
        return r.choice([("NoCoupon",), ("Percent", r.choice([0, 1, 10, 25, 50])), ("Fixed", r.choice([0, 1, 500, 100000, 10**9])), ("FreeShipping",)])
    out = []
    small = lambda: {"sku": "a", "cat": r.choice(CATEGORIES), "qty": r.randint(1, 3), "unit": r.randint(1, 3000), "grams": r.choice([0, 200, 900, 1500, 4000, 7000])}
    for k in range(n):
        kind = k % 10
        lines = [line() for _ in range(r.randint(1, 6))]
        cu, co = customer(), coupon()
        if kind == 0:
            lines = []
        elif kind == 1:
            lines[r.randrange(len(lines))] = line(bad=True)
        elif kind == 2:
            cu = ("Member", -1)
        elif kind == 3:
            co = r.choice([("Percent", -1), ("Percent", 51), ("Fixed", -1)])
        elif kind in (4, 5, 6):  # amounts near the thresholds of shipping, where its rules show
            lines = [small() for _ in range(r.randint(1, 4))]
        out.append({"lines": lines, "customer": cu, "coupon": co, "country": r.choice(["FR", "FR", "DE", ""])})
    out.append({"lines": [line() for _ in range(1001)], "customer": ("Guest",), "coupon": ("NoCoupon",), "country": "FR"})
    # exactly on the thresholds, where a `<` for a `<=` shows
    one = lambda cat, qty, unit, grams: {"sku": "b", "cat": cat, "qty": qty, "unit": unit, "grams": grams}
    for sub in (99999, 100000, 100001):
        out.append({"lines": [one("Book", 1, sub, 0)], "customer": ("Business", "FR1"), "coupon": ("NoCoupon",), "country": "FR"})
    for g in (0, 1, 999, 1000, 1001, 4999, 5000, 5001, 5999, 6000, 6001):
        out.append({"lines": [one("Standard", 1, 100, g)], "customer": ("Guest",), "coupon": ("NoCoupon",), "country": "FR"})
    for u in (4999, 5000, 5001, 9999, 10000, 10001):
        for cu in (("Guest",), ("Member", 1)):
            out.append({"lines": [one("Medicine", 1, u, 700)], "customer": cu, "coupon": ("NoCoupon",), "country": "FR"})
    for q in (9, 10, 11, 99, 100, 101):
        out.append({"lines": [one("Food", q, 1000, 0)], "customer": ("Guest",), "coupon": ("NoCoupon",), "country": "FR"})
    for y in (4, 5):
        out.append({"lines": [one("Book", 1, 10000, 0)], "customer": ("Member", y), "coupon": ("NoCoupon",), "country": "FR"})
    # the largest order there can be: what fits in i64 must be proved, not hoped
    biggest = {"sku": "x", "cat": "Standard", "qty": 10000, "unit": 100000000, "grams": 1000000}
    out.append({"lines": [biggest] * 1000, "customer": ("Guest",), "coupon": ("NoCoupon",), "country": "FR"})
    return out


def hidden_python(directory: Path) -> dict[str, Any]:
    sys.path.insert(0, str(directory))
    sys.setrecursionlimit(10000)
    try:
        import catalog, discounts, solution
    except Exception as e:
        return {"loaded": False, "error": repr(e)[:300]}
    passed, total, first = 0, 0, None
    for o in cases(20261106, 400):
        total += 1
        try:
            lines = []
            for x in o["lines"]:
                lines.append(catalog.Line(x["sku"], getattr(catalog, x["cat"])(), x["qty"], x["unit"], x["grams"]))
        except ValueError:  # a value out of i32 is refused when built: the type says so before the rules can
            passed += 1
            continue
        cu = getattr(discounts, o["customer"][0])(*o["customer"][1:])
        co = getattr(discounts, o["coupon"][0])(*o["coupon"][1:])
        try:
            g = solution.price(solution.Order(lines, cu, co, o["country"]))
            w = oracle(o)
            if type(g).__name__.endswith("_Ok"):
                i = g.f0
                got = ("ok", i.subtotal, i.discount, i.net, i.shipping, i.vat, i.total)
            else:
                got = ("err", g.f0)
        except Exception as e:
            got = ("raised", repr(e)[:120])
            w = oracle(o)
        if got == w:
            passed += 1
        elif first is None:
            first = {"want": w, "got": got, "lines": len(o["lines"]), "customer": o["customer"], "coupon": o["coupon"], "country": o["country"]}
    return {"loaded": True, "total": total, "passed": passed, "first_failure": first}


def cs_literal(o: dict[str, Any]) -> str:
    def lit(s: str) -> str:
        return '"' + s + '"'

    def customer():
        c = o["customer"]
        return "new D.Customer." + c[0] + "(" + (str(c[1]) if c[0] == "Member" else lit(c[1]) if c[0] == "Business" else "") + ")"

    def coupon():
        c = o["coupon"]
        return "new D.Coupon." + c[0] + "(" + (str(c[1]) if len(c) > 1 else "") + ")"
    lines = ", ".join(f'new C.Line({lit(x["sku"])}, new C.Category.{x["cat"]}(), {x["qty"]}, {x["unit"]}, {x["grams"]})' for x in o["lines"])
    return f"new Solution.Order(new C.Line[] {{ {lines} }}, {customer()}, {coupon()}, {lit(o['country'])})"


def hidden_csharp(work: Path, quod: str, variant: str) -> dict[str, Any]:
    """The same oracle, on the C# compiled for .NET Framework 4.7.2 with C# 7.3, through what a C# caller writes."""
    if variant != "i64":
        return {"skipped": "only the i64 variant has a C# driver"}
    out = Path(tempfile.mkdtemp())
    g = sh([quod, "build", "solution.quod", "--target", "csharp", "-o", str(out), "--require-contracts"], work, 600)
    if g["code"] != 0:
        return {"compiled": False, "error": "not generated: " + (g["out"] + g["err"])[-200:]}
    try:
        chosen = [c for c in cases(20261106, 200) if len(c["lines"]) <= 6 or len(c["lines"]) == 1000]
        lines = []
        for k, o in enumerate(chosen):
            w = oracle(o)
            want = "|".join(str(x) for x in w)
            lines.append(f'Run({k}, () => {cs_literal(o)}, "{want}");')
        program = """using System;
using System.Collections.Generic;
using Quod.Generated;
using C = Quod.Generated.Catalog;
using D = Quod.Generated.Discounts;
class P {
  static int ok, bad; static string first;
  static void Run(int k, Func<Solution.Order> build, string want) {
    string got;
    try {
      var r = Solution.Price(build());
      got = r.Match<string>(i => "ok|" + i.Subtotal + "|" + i.Discount + "|" + i.Net + "|" + i.Shipping + "|" + i.Vat + "|" + i.Total, e => "err|" + e);
    } catch (ArgumentException) { got = want.StartsWith("err") ? want : "raised"; }
    catch (Exception e) { got = "raised " + e.GetType().Name; }
    if (got == want) ok++; else { bad++; if (first == null) first = k + ": want " + want + " got " + got; }
  }
  static void Main() {
""" + "\n".join("    " + x for x in lines) + """
    Console.WriteLine(ok + " " + (ok + bad) + " " + first);
  }
}
"""
        (out / "Program.cs").write_text(program, encoding="utf-8")
        (out / "p.csproj").write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net472</TargetFramework><LangVersion>7.3</LangVersion><EnableDefaultCompileItems>false</EnableDefaultCompileItems><AppendTargetFrameworkToOutputPath>false</AppendTargetFrameworkToOutputPath></PropertyGroup><ItemGroup><Compile Include="*.cs" /><Reference Include="System.Numerics" /></ItemGroup></Project>\n', encoding="utf-8")
        c = sh("dotnet build -c Release -v q -nologo", out, 400)
        if c["code"] != 0:
            return {"compiled": False, "error": str(sorted(set(re.findall(r"[A-Za-z0-9_.]+\.cs\(\d+,\d+\): error CS\d+: .{0,110}", c["out"])))[:3])}
        x = sh([str(out / "bin/Release/p.exe")], out, 300)
        parts = x["out"].strip().split(" ", 2)
        return {"compiled": True, "passed": int(parts[0]), "total": int(parts[1]), "first_failure": parts[2] if len(parts) > 2 else None} if len(parts) >= 2 else {"compiled": True, "error": (x["out"] + x["err"])[-300:]}
    finally:
        shutil.rmtree(out, ignore_errors=True)


def client_properties(work: Path, quod: str) -> dict[str, Any]:
    d = Path(tempfile.mkdtemp())
    try:
        for f in work.glob("*.quod"):
            shutil.copy(f, d)
        (d / "client.quod").write_text(CLIENT, encoding="utf-8")
        r = sh([quod, "check", "client.quod", "--timeout", "30", "--budget", "300"], d, 400)
        text = r["out"] + r["err"]
        failed = sorted({m for m in re.findall(r"error: in (p_[a-z]+)", text)})
        if "syntax or type error" in text or (r["code"] != 0 and not failed):
            return {"error": text[-300:]}
        return {p: p not in failed for p in PROPERTIES}
    finally:
        shutil.rmtree(d, ignore_errors=True)


def evaluate(work: Path, quod: str, variant: str) -> dict[str, Any]:
    work = work.resolve()
    res: dict[str, Any] = {"submitted": (work / "solution.quod").exists()}
    if not res["submitted"]:
        return res
    text = "\n".join(p.read_text(encoding="utf-8", errors="replace") for p in work.glob("*.quod"))
    res["lines"] = text.count("\n")
    res["lemmas"] = len(re.findall(r"^\s*lemma ", text, re.M))
    res["loops"] = len(re.findall(r"\bwhile\b", text))
    res["loose"] = len(re.findall(r"\bloose\b", text))
    v = sh([quod, "check", "solution.quod", "--require-contracts"], work, 900)
    res["verified"] = v["code"] == 0
    res["check_secs"] = v["secs"]
    res["check_tail"] = (v["out"] + v["err"])[-600:]
    build = work / "_py"
    shutil.rmtree(build, ignore_errors=True)
    b = sh([quod, "build", "solution.quod", "-o", str(build), "--require-contracts"], work, 900)
    if b["code"] == 0:
        h = sh([sys.executable, "-m", "verifbench.billing", "--hidden", str(build)], Path(__file__).resolve().parent.parent, 600)
        try:
            res["hidden"] = json.loads(h["out"].strip().splitlines()[-1])
        except (IndexError, json.JSONDecodeError):
            res["hidden"] = {"loaded": False, "error": (h["err"] or h["out"])[-300:]}
        res["client"] = client_properties(work, quod)
        res["csharp"] = hidden_csharp(work, quod, variant)
    else:
        res["hidden"] = {"loaded": False, "error": "not built: " + (b["out"] + b["err"])[-300:]}
    h = res.get("hidden") or {}
    res["all_pass"] = bool(h.get("loaded")) and h.get("total") == h.get("passed")
    return res


def one(variant: str, model: str, trial: int, out: Path, quod: str, timeout: int, lock: threading.Lock, stop: threading.Event) -> None:
    if stop.is_set():
        return
    work = out / "work" / f"{variant}__{model}__{trial}"
    shutil.rmtree(work, ignore_errors=True)
    work.mkdir(parents=True)
    (work / ".mcp.json").write_text(json.dumps({"mcpServers": {"quod": {"command": quod, "args": ["mcp", "--require-contracts"]}}}), encoding="utf-8")
    tools = "Read,Write,Edit,Glob,Grep," + ",".join("mcp__quod__" + t for t in ("quod_check", "quod_run", "quod_build", "quod_reference"))
    cmd = f'claude -p --output-format stream-json --verbose --model {model} --permission-mode acceptEdits --mcp-config ".mcp.json" --strict-mcp-config --allowedTools "{tools}"'
    q, a = ("i32", "i64") if variant == "i64" else ("int", "int")
    prompt = PROMPT.format(spec=SPEC, sig=SIG.replace("{q}", q).replace("{a}", a))
    r = sh(cmd, work, timeout, stdin=prompt)
    (work / "agent_stdout.jsonl").write_text(r["out"], encoding="utf-8")
    (work / "agent_stderr.txt").write_text(r["err"], encoding="utf-8")
    m = parse_events(r["out"])
    text = (m.get("result_text") or "").lower()
    limit = bool(m.get("agent_error")) and any(w in text for w in ("usage limit", "rate limit", "limit reached", "429", "quota"))
    row = {"variant": variant, "model": model, "trial": trial, "secs": r["secs"], "exit": r["code"], "limit": limit, **m, **evaluate(work, quod, variant)}
    with lock:
        with open(out / "results.jsonl", "a", encoding="utf-8") as f:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")
        print(variant, model, trial, "verified", row.get("verified"), "hidden", (row.get("hidden") or {}).get("passed"), "/", (row.get("hidden") or {}).get("total"), "client", row.get("client"), "cs", (row.get("csharp") or {}).get("passed"), "secs", r["secs"], "checks", m["calls"].get("quod_check"), "cost", m.get("cost_usd"), flush=True)
    if limit:
        stop.set()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--run", type=Path)
    p.add_argument("--models", default="claude-haiku-5-5")
    p.add_argument("--variants", default="i64,int")
    p.add_argument("--trials", type=int, default=3)
    p.add_argument("--workers", type=int, default=3)
    p.add_argument("--timeout", type=int, default=2400)
    p.add_argument("--quod", default=None)
    p.add_argument("--selfcheck", type=Path)
    p.add_argument("--hidden", type=Path)
    a = p.parse_args()
    if a.hidden:
        print(json.dumps(hidden_python(a.hidden)))
        return
    quod = a.quod or str(Path(__file__).resolve().parents[2] / "artifacts" / "aot-0.3.1" / "quod.exe")
    if a.selfcheck:
        print(json.dumps(evaluate(a.selfcheck, quod, "i64"), ensure_ascii=False, indent=1))
        return
    a.run.mkdir(parents=True, exist_ok=True)
    done = set()
    if (a.run / "results.jsonl").exists():
        for line in (a.run / "results.jsonl").read_text(encoding="utf-8").splitlines():
            row = json.loads(line)
            if not row.get("limit"):
                done.add((row["variant"], row["model"], row["trial"]))
    jobs = [(v, m, k) for k in range(a.trials) for m in a.models.split(",") for v in a.variants.split(",") if (v, m, k) not in done]
    lock, stop = threading.Lock(), threading.Event()
    with futures.ThreadPoolExecutor(a.workers) as pool:
        for f in futures.as_completed([pool.submit(one, v, m, k, a.run, quod, a.timeout, lock, stop) for v, m, k in jobs]):
            f.result()
    print("stopped on a usage limit" if stop.is_set() else "done")


if __name__ == "__main__":
    main()
