"""Is a contract sound? Whether it lets through a result the task forbids, measured on small inputs, without
the code of the solution and without a judge: the main measure of bench/heldout.md.

    python -m verifbench.adequacy runs/<run>           # every accepted Quod or Dafny solution of a run
    python -m verifbench.adequacy runs/<run> --max-wrong 0 --time-limit 60 --all-submitted --out adequacy-v2.jsonl

For each input: its `requires` must accept it, its `ensures` must reject every wrong result, and accept every
result the task allows. A contract is *sound* if nothing fails on the first two, *exact* if nothing fails at all.
A finite test: it can show that a contract is not sound, with a witness, not that it is.

Quod contracts are evaluated (`quod contract`). A Dafny contract is compiled and run if it can be; otherwise each
question is proved, in both directions. What no tool answers is *unknown*. A contract with an unknown `requires` or wrong
result is *undecided* (`sound` is null), neither sound nor unsound: that goes to the judge, and is reported. An unknown
on an allowed result says nothing of soundness: it leaves `exact` null.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from verifbench.completeness import extract_contract
from verifbench.tasks import TASKS, hidden_cases, normalize, validate
from verifbench.witness import lit, parse_type

QUOD_EXE = os.environ.get("QUOD_EXE", "quod")
SEED = 20261104
MAX_INPUTS = 14
MAX_WRONG = 8  # 0: all of them
TIME_LIMIT = 10  # seconds per proof of a Dafny question


def mutations(v: Any, r_budget: int = 2) -> list[Any]:
    """Results close to `v`, in its normalized form."""
    out: list[Any] = []
    if isinstance(v, bool):
        return [not v]
    if isinstance(v, int):
        return [v + 1, v - 1, 0, -1, -v, 2 * v]
    if isinstance(v, list):
        out += [[], v + v[:1], v[:-1], v[1:], v[::-1], [x for i, x in enumerate(v) if i != len(v) // 2]]
        if v and isinstance(v[0], int):
            out.append(v + [v[-1] + 1])
        for i in range(len(v)):
            for m in mutations(v[i], r_budget - 1)[:2] if r_budget > 0 else []:
                out.append(v[:i] + [m] + v[i + 1:])
        return out
    return out


def pairs_of(n: int) -> list[list[int]]:
    return [[i, j] for i in range(n) for j in range(i + 1, n)] + [[-1, -1]]


def inputs_of(task) -> list[tuple]:
    cases = hidden_cases(task, SEED, 200)
    # the edge cases, then random ones of growing size: small enough for Dafny to prove on literals
    edge = list(task.edge_cases)[:MAX_INPUTS // 2]
    rest = sorted(cases[len(task.edge_cases):], key=lambda a: len(repr(a)))
    step = max(1, len(rest[:80]) // (MAX_INPUTS - len(edge)))
    return edge + rest[:80][::step][:MAX_INPUTS - len(edge)]


def results_of(task, args: tuple) -> tuple[list[Any], list[Any]]:
    """The results the task allows on this input that we can name, and wrong ones."""
    if task.oracle is not None:
        allowed = [normalize(task.oracle(*args))]
    else:
        allowed = []
    candidates: list[Any] = list(allowed)
    if task.id == "two_sum_sorted":
        candidates = pairs_of(len(args[0]))
    elif task.id == "binary_search":
        candidates = list(range(-1, len(args[0])))
    if task.oracle is None:
        allowed = [c for c in candidates if validate(task, args, c) is None]
    seen = {repr(a) for a in allowed}
    returns = task.py_signature.rsplit("->", 1)[1].strip()
    wrong = []
    pool = [c for c in candidates if repr(c) not in seen]
    for a in allowed:
        pool += mutations(a)
    pool += samples(returns)
    for c in pool:
        key = repr(c)
        if key in seen or not fits(c, returns):
            continue
        seen.add(key)
        try:
            if validate(task, args, c) is not None:
                wrong.append(c)
        except Exception:  # noqa: BLE001 - the oracle cannot judge this shape: it is not a candidate
            continue
    return allowed, wrong[:MAX_WRONG] if MAX_WRONG else wrong


def _split_top(text: str) -> list[str]:
    parts, depth, current = [], 0, ""
    for c in text:
        if c == "," and depth == 0:
            parts.append(current.strip())
            current = ""
            continue
        depth += c == "["
        depth -= c == "]"
        current += c
    parts.append(current.strip())
    return parts


def fits(value: Any, t: str) -> bool:
    """Is this a value of the Python type `t`, tuples being lists once normalized?"""
    if t == "int":
        return isinstance(value, int) and not isinstance(value, bool)
    if t == "bool":
        return isinstance(value, bool)
    m = re.fullmatch(r"list\[(.*)\]", t)
    if m:
        return isinstance(value, list) and all(fits(x, m.group(1)) for x in value)
    m = re.fullmatch(r"tuple\[(.*)\]", t)
    if m:
        ts = _split_top(m.group(1))
        return isinstance(value, list) and len(value) == len(ts) and all(fits(x, y) for x, y in zip(value, ts))
    return False


def samples(t: str) -> list[Any]:
    """A few small values of a type: an empty right answer has nothing to mutate."""
    if t == "int":
        return [0, 1, -1]
    if t == "bool":
        return [True, False]
    m = re.fullmatch(r"list\[(.*)\]", t)
    if m:
        return [[x] for x in samples(m.group(1))] + [samples(m.group(1))[:2]]
    m = re.fullmatch(r"tuple\[(.*)\]", t)
    if m:
        return [[samples(x)[k % len(samples(x))] for x in _split_top(m.group(1))] for k in range(3)]
    return []


def plan(task) -> list[dict]:
    return [dict(zip(("args", "allowed", "wrong"), (normalize(list(a)), *results_of(task, a)))) for a in inputs_of(task)]


def verdict(cases: list[dict]) -> dict:
    """cases: each with `requires` and `allowed`, `wrong`: lists of true, false or null."""
    rejected_inputs, accepted_wrong, rejected_allowed, unknown_sound, unknown_allowed, total = [], [], [], 0, 0, 0
    for c in cases:
        total += 1 + len(c["allowed_v"]) + len(c["wrong_v"])
        unknown_sound += sum(v is None for v in [c["requires"], *c["wrong_v"]])
        unknown_allowed += sum(v is None for v in c["allowed_v"])
        if c["requires"] is False:
            rejected_inputs.append(c["args"])
            continue
        accepted_wrong += [(c["args"], r) for r, v in zip(c["wrong"], c["wrong_v"]) if v is True]
        rejected_allowed += [(c["args"], r) for r, v in zip(c["allowed"], c["allowed_v"]) if v is False]
    unsound = bool(rejected_inputs or accepted_wrong)
    # a contract with unknown questions is not called sound: no tool answered
    sound = False if unsound else (True if unknown_sound == 0 else None)
    exact = False if unsound or rejected_allowed else (True if sound and unknown_allowed == 0 else None)
    return {"sound": sound, "exact": exact, "unknown": unknown_sound + unknown_allowed, "unknown_sound": unknown_sound,
            "unknown_allowed": unknown_allowed, "pairs": total,
            "rejected_input": rejected_inputs[:2], "accepted_wrong": accepted_wrong[:2], "rejected_allowed": rejected_allowed[:2]}


# --- Quod -------------------------------------------------------------------------------------------

def quod_cases(task, solution: Path) -> list[dict]:
    cases = plan(task)
    request = [{"args": c["args"], "results": c["allowed"] + c["wrong"]} for c in cases]
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "cases.json"
        f.write_text(json.dumps(request), encoding="utf-8")
        r = subprocess.run([QUOD_EXE, "contract", str(solution), str(f), "--function", task.func],
                           capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=600)
    if r.returncode != 0:
        raise RuntimeError(r.stderr[-400:])
    for c, a in zip(cases, json.loads(r.stdout)):
        if "error" in a:
            raise RuntimeError(a["error"])
        c["requires"] = a["requires"]
        c["allowed_v"] = a["results"][:len(c["allowed"])]
        c["wrong_v"] = a["results"][len(c["allowed"]):]
    return cases


# --- Dafny: run the contract when it compiles, otherwise a lemma per question -----------------------------

def _questions(task, contract: dict, cases: list[dict]) -> list[tuple[int, str, int, str]]:
    types = [parse_type(t) for _, t in contract["params"]]
    out_type = parse_type(contract["outs"][0][1])
    out = []
    for i, c in enumerate(cases):
        args = ", ".join(lit(a, t) for a, t in zip(c["args"], types))
        out.append((i, "requires", 0, f"Req__({args})"))
        for kind, results in (("allowed", c["allowed"]), ("wrong", c["wrong"])):
            for k, r in enumerate(results):
                try:
                    out.append((i, kind, k, f"Ens__({args}, {lit(r, out_type)})"))
                except (ValueError, TypeError):
                    continue
    return out


def _predicates(contract: dict, keyword: str) -> str:
    signature = ", ".join(f"{n}: {t}" for n, t in contract["params"] + contract["outs"])
    ps = ", ".join(f"{n}: {t}" for n, t in contract["params"])
    req = " && ".join(f"({r})" for r in contract["requires"]) or "true"
    ens = " && ".join(f"({e})" for e in contract["ensures"]) or "true"
    return f"  {keyword} Req__({ps}) {{ {req} }}\n  {keyword} Ens__({signature}) {{ {ens} }}\n"


def _run_compiled(src: str, contract: dict, questions: list, d: Path) -> dict[int, bool] | None:
    """The verdict of each question by running it, None if the contract does not compile (an unbounded
    quantifier). A question that crashes (a helper called outside its requires) stays without a verdict."""
    known: dict[int, bool] = {}
    start = 0
    plain = re.sub(r"\bghost\s+(?=(predicate|function)\b)", "", src)
    for _ in range(6):  # a crash stops the program: go on after it, a few times
        body = "\n".join(f'    print "@{n} ", {q[3]}, "\\n";' for n, q in enumerate(questions) if n >= start)
        end = plain.rstrip().rfind("}")
        text = plain[:end] + "\n" + _predicates(contract, "predicate") + "  method Main() {\n" + body + "\n  }\n" + plain[end:]
        f = d / "run.dfy"
        f.write_text(text, encoding="utf-8")
        r = subprocess.run(["dafny", "run", "run.dfy", "--no-verify", "--allow-warnings"], cwd=d, capture_output=True,
                           text=True, encoding="utf-8", errors="replace", timeout=600)
        lines = re.findall(r"^@(\d+) (true|false)\s*$", r.stdout, re.M)
        if not lines and start == 0:
            return None
        for n, v in lines:
            known[int(n)] = v == "true"
        last = max((int(n) for n, _ in lines), default=start - 1)
        if r.returncode == 0 or last + 2 >= len(questions):
            return known
        start = last + 2  # the one after the crash
    return known


def _prove(src: str, contract: dict, questions: list, d: Path, only: set[int]) -> dict[int, bool]:
    gen = [_predicates(contract, "ghost predicate")]
    for n, q in enumerate(questions):
        if n in only:
            gen.append(f"  lemma Q{n}__yes() ensures {q[3]} {{ }}\n  lemma Q{n}__no() ensures !({q[3]}) {{ }}")
    end = src.rstrip().rfind("}")
    text = src[:end] + "\n" + "\n".join(gen) + "\n" + src[end:]
    f = d / "check.dfy"
    f.write_text(text, encoding="utf-8")
    r = subprocess.run(["dafny", "verify", "check.dfy", "--allow-warnings", "--verification-time-limit", str(TIME_LIMIT),
                        "--filter-symbol", "__"], cwd=d, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=7200)
    lines = text.splitlines()
    failed = set()
    for m in re.finditer(r"\((\d+),\d+\): Error", r.stdout):
        found = re.search(r"lemma Q(\d+)__(yes|no)\(", lines[int(m.group(1)) - 1])
        if found:
            failed.add((int(found.group(1)), found.group(2)))
    known = {}
    for n in only:
        yes, no = (n, "yes") not in failed, (n, "no") not in failed
        if yes != no:
            known[n] = yes
    return known


def dafny_cases(task, solution: Path) -> list[dict]:
    src = solution.read_text(encoding="utf-8", errors="replace")
    contract = extract_contract(src, task.func)
    cases = plan(task)
    questions = _questions(task, contract, cases)
    with tempfile.TemporaryDirectory() as tmp:
        d = Path(tmp)
        known = _run_compiled(src, contract, questions, d) or {}
        missing = {n for n in range(len(questions)) if n not in known}
        if missing:
            known.update(_prove(src, contract, questions, d, missing))
    for c in cases:
        c["requires"], c["allowed_v"], c["wrong_v"] = None, [None] * len(c["allowed"]), [None] * len(c["wrong"])
    for n, (i, kind, k, _) in enumerate(questions):
        v = known.get(n)
        if kind == "requires":
            cases[i]["requires"] = v
        else:
            cases[i][kind + "_v"][k] = v
    return cases


def measure(run: Path, all_submitted: bool = False) -> list[dict]:
    rows = []
    for line in (run / "results.jsonl").read_text(encoding="utf-8").splitlines():
        r = json.loads(line)
        if r["arm"] == "python" or not (r.get("accepted") or (all_submitted and r["eval"].get("submitted"))):
            continue
        task = TASKS[r["task"]]
        wd = run / "work" / Path(r["workdir"]).name
        try:
            if r["arm"].startswith("quod"):
                cases = quod_cases(task, wd / "solution.quod")
            else:
                cases = dafny_cases(task, wd / "solution.dfy")
            row = verdict(cases)
        except Exception as e:  # noqa: BLE001 - reported: a contract we could not measure is not a sound one
            row = {"error": f"{type(e).__name__}: {e}"[:300], "sound": None, "exact": None}
        row.update({"task": r["task"], "arm": r["arm"], "trial": r["trial"], "accepted": r.get("accepted"), "all_pass": r.get("all_pass")})
        rows.append(row)
        print(json.dumps(row), flush=True)
    return rows


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+", type=Path)
    ap.add_argument("--max-wrong", type=int, default=MAX_WRONG, help="wrong results per input, 0 for all of them")
    ap.add_argument("--time-limit", type=int, default=TIME_LIMIT, help="seconds per proof of a Dafny question")
    ap.add_argument("--all-submitted", action="store_true", help="also the solutions that were not accepted")
    ap.add_argument("--out", default="adequacy.jsonl")
    a = ap.parse_args()
    MAX_WRONG, TIME_LIMIT = a.max_wrong, a.time_limit
    for run in a.runs:
        rows = measure(run, a.all_submitted)
        (run / a.out).write_text("".join(json.dumps(r) + "\n" for r in rows), encoding="utf-8", newline="\n")
