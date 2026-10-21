"""Witness search for specs the completeness check could not prove unique.

For small concrete inputs x, take the correct answer a (from the selfcheck GOOD solutions) and
neighbouring candidates b != a, then ask Dafny to prove Post(x, a) and Post(x, b) on literals.
Both proved => a certain witness that the spec admits two results ("underspecified").
No witness => "inconclusive" (spec may be complete; the uniqueness proof is just too hard).
An unproved Post(x, a) is NOT a refutation: Dafny may just fail to unfold recursive definitions.

    python -m verifbench.witness          # uses completeness/results.json
"""
from __future__ import annotations

import json
import random
import re
import subprocess
from pathlib import Path
from typing import Any

from verifbench.completeness import OUT, ROOT, build_check, extract_contract
from verifbench.selfcheck import GOOD
from verifbench.tasks import TASKS

MAX_INPUTS, MAX_CANDIDATES = 6, 14


# --- Dafny types and literals -------------------------------------------------

def parse_type(t: str) -> Any:
    """'seq<(int, int)>' -> ('seq', ('tuple', ['int', 'int'])); 'string' -> 'string'."""
    t = t.strip()
    if t.startswith("seq<") and t.endswith(">"):
        return ("seq", parse_type(t[4:-1]))
    if t.startswith("(") and t.endswith(")"):
        parts, depth, cur = [], 0, ""
        for c in t[1:-1]:
            depth += c in "(<"
            depth -= c in ")>"
            if c == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += c
        parts.append(cur)
        return ("tuple", [parse_type(p) for p in parts])
    return t  # int, bool, string, nat


def lit(v: Any, t: Any) -> str:
    if t == "bool":
        return "true" if v else "false"
    if t in ("int", "nat"):
        return f"({v})" if v < 0 else str(v)
    if t == "string":
        return '"' + v.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(t, tuple) and t[0] == "seq":
        return "[" + ", ".join(lit(x, t[1]) for x in v) + "]"
    if isinstance(t, tuple) and t[0] == "tuple":
        return "(" + ", ".join(lit(x, s) for x, s in zip(v, t[1])) + ")"
    raise ValueError(f"unsupported type {t!r}")


# --- Candidate neighbours of a correct answer ---------------------------------

def _alt_char(c: str) -> str:
    if c.isdigit():
        return str((int(c) + 1) % 10)
    if c == " ":
        return "x"
    return "b" if c != "b" else "c"


def neighbours(v: Any, t: Any) -> list[Any]:
    if t == "bool":
        return [not v]
    if t in ("int", "nat"):
        return [v + 1, v - 1, 0, -v]
    if t == "string":
        out = [v + "x", v + "1", v[:-1], ""]
        for i in sorted({0, len(v) // 2, len(v) - 1}):
            if 0 <= i < len(v):
                out.append(v[:i] + _alt_char(v[i]) + v[i + 1:])
        return out
    if isinstance(t, tuple) and t[0] == "seq":
        v = list(v)
        out = [[], v[:-1], v[::-1]]
        if v:
            out.append(v + [v[-1]])
            for i in sorted({0, len(v) - 1}):
                for alt in neighbours(v[i], t[1])[:2]:
                    out.append(v[:i] + [alt] + v[i + 1:])
        return out
    if isinstance(t, tuple) and t[0] == "tuple":
        out = []
        for i, s in enumerate(t[1]):
            for alt in neighbours(v[i], s)[:2]:
                out.append(tuple(v[:i]) + (alt,) + tuple(v[i + 1:]))
        return out
    return []


def canon(v: Any) -> Any:
    if isinstance(v, (list, tuple)):
        return tuple(canon(x) for x in v)
    return v


# --- Search --------------------------------------------------------------------

def small_inputs(task) -> list[tuple]:
    cands = [c for c in task.edge_cases if len(repr(c)) <= 90]
    r = random.Random(f"witness:{task.id}")
    cands += [c for c in (task.random_case(r) for _ in range(200)) if len(repr(c)) <= 60][:20]
    seen, out = set(), []
    for c in cands:
        if repr(c) not in seen:
            seen.add(repr(c))
            out.append(c)
    return out[:MAX_INPUTS]


def solve(task, args: tuple) -> Any:
    ns: dict[str, Any] = {}
    exec(GOOD[task.id], ns)  # noqa: S102 - our own reference solutions
    return ns[task.func](*args)


def search(row: dict) -> dict:
    task = TASKS[row["task"]]
    run = ROOT / "runs" / row["run"]
    rec = next(json.loads(l) for l in (run / "results.jsonl").read_text(encoding="utf-8").splitlines()
               if json.loads(l)["task"] == row["task"] and json.loads(l)["arm"] == "dafny"
               and json.loads(l).get("model", "default") == row["model"])
    src = (run / "work" / Path(rec["workdir"]).name / "solution.dfy").read_text(encoding="utf-8")
    c = extract_contract(src, task.func)
    ptypes = [parse_type(t) for _, t in c["params"]]
    otypes = [parse_type(t) for _, t in c["outs"]]
    otype = otypes[0] if len(otypes) == 1 else ("tuple", otypes)

    lemmas, meta = [], {}
    for xi, x in enumerate(small_inputs(task)):
        a = solve(task, x)
        args = ", ".join(lit(v, t) for v, t in zip(x, ptypes))

        def post(val: Any) -> str:
            vals = [val] if len(otypes) == 1 else list(val)
            return f"Post__({args}, " + ", ".join(lit(v, t) for v, t in zip(vals, otypes)) + ")"

        lemmas.append((f"W__a_{xi}", post(a)))
        meta[f"W__a_{xi}"] = (x, a, None)
        seen = {canon(a)}
        bs = [b for b in neighbours(a, otype) if not (canon(b) in seen or seen.add(canon(b)))]
        for bi, b in enumerate(bs[:MAX_CANDIDATES]):
            name = f"W__b_{xi}_{bi}"
            lemmas.append((name, post(b)))
            meta[name] = (x, a, b)

    base = build_check(src, c)
    end = base.rstrip().rfind("}")
    head = base[:end]
    spans, body = {}, ""
    line = head.count("\n") + 1
    for name, goal in lemmas:
        text = f"\n  lemma {name}()\n    ensures {goal}\n  {{\n  }}\n"
        spans[name] = (line + 1, line + 4)
        line += text.count("\n")
        body += text
    dst = OUT / f"witness__{row['file']}"
    dst.write_text(head + body + base[end:], encoding="utf-8")

    p = subprocess.run(["dafny", "verify", dst.name, "--allow-warnings", "--filter-symbol", "W__",
                        "--verification-time-limit", "20"], cwd=dst.parent, capture_output=True,
                       text=True, encoding="utf-8", errors="replace", timeout=1800)
    failed_lines = {int(m.group(1)) for m in
                    re.finditer(rf"{re.escape(dst.name)}\((\d+),\d+\): Error", p.stdout + p.stderr)}
    failed = {n for n, (lo, hi) in spans.items() if any(lo <= l <= hi for l in failed_lines)}

    a_ok = {n for n in meta if n.startswith("W__a_") and n not in failed}
    a_unproved = [meta[n][0] for n in meta if n.startswith("W__a_") and n in failed]
    for name, (x, a, b) in meta.items():
        xi = name.split("_")[3] if name.startswith("W__b_") else None
        if b is not None and name not in failed and f"W__a_{xi}" in a_ok:
            return {"verdict": "underspecified", "input": repr(x), "result_a": repr(a),
                    "result_b": repr(b), "a_unproved": len(a_unproved), "lemmas": len(lemmas)}
    return {"verdict": "inconclusive", "a_proved": len(a_ok), "a_unproved": len(a_unproved),
            "lemmas": len(lemmas)}


def main() -> None:
    rows = json.loads((OUT / "results.json").read_text(encoding="utf-8"))
    for row in rows:
        if row["status"] == "determined":
            continue
        row["witness"] = search(row)
        w = row["witness"]
        print(f"{row['run']:6} {row['task']:16} {row['model']:8} {w['verdict']:15}"
              + (f" x={w['input']}  a={w['result_a']}  b={w['result_b']}"
                 if w["verdict"] == "underspecified"
                 else f" (Post(x,a) proved on {w['a_proved']} inputs, not proved on {w['a_unproved']})"),
              flush=True)
    (OUT / "results.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
