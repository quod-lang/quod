"""Mutant bench: how quod check rejects small bugs in verified programs.

Each mutant changes one operator or constant in the code of a verified Quod program (never in
its contracts). quod check must reject it, ideally with a counterexample:

- refuted: a proof error with a counterexample (the agent knows what input breaks what), run or
  from the solver, or a completeness witness;
- unconfirmed: rejected with a counterexample that neither the solver nor a run confirms;
- no hint: rejected, but without any counterexample (typically a solver timeout);
- survived: verified anyway (an equivalent mutant, or a contract that does not see the bug);
- invalid: the mutant does not parse or type-check (e.g. `>` mutated in `seq<int>`): not counted;
- hung: quod check did not finish within --timeout seconds (killed).

    python -m verifbench.mutants quod/*/solution.quod --max 15 --out runs/mutants1.jsonl
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import statistics
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUOD = os.environ.get("QUOD_EXE") or str(
    ROOT.parent / "artifacts" / "aot" / ("quod.exe" if os.name == "nt" else "quod"))

# (pattern, replacement): one occurrence is replaced per mutant
OPERATORS = [
    (r"(?<![<>=!])<=(?!=)", "<"), (r"(?<![<>=!-])<(?![=-])", "<="),
    (r"(?<![<>=!-])>=", ">"), (r"(?<![<>=!-])>(?![=>])", ">="),
    (r"==(?!>)", "!="), (r"!=", "=="),
    (r"\+ 1\b", "+ 2"), (r"- 1\b", "- 2"), (r"\+ 1\b", "- 1"),
    (r"(?<![\w.])0(?![\w.])", "1"), (r"(?<![\w.])1(?![\w.])", "0"),
    (r"&&", "||"),
]

# Signatures and contracts are not mutated: only the code is (a `lemma` signature, like a `fn`
# one, would only yield mutants that do not parse).
CONTRACT = re.compile(r"^\s*(fn |lemma |requires|ensures|invariant|decreases|loose|//)")


def mutants(source: str) -> list[tuple[str, str]]:
    """Every single-site mutation of the code lines: (description, mutated source)."""
    lines = source.split("\n")
    out = []
    for i, line in enumerate(lines):
        code = line.split("//")[0]
        if CONTRACT.match(line) or not code.strip():
            continue
        for pattern, repl in OPERATORS:
            for m in re.finditer(pattern, code):
                mutated = code[:m.start()] + re.sub(pattern, repl, m.group(0), count=1) + code[m.end():]
                if mutated == code:
                    continue
                new_lines = lines.copy()
                new_lines[i] = mutated + line[len(code):]
                out.append((f"line {i + 1}: {code.strip()}  ->  {mutated.strip()}", "\n".join(new_lines)))
    return out


def check(path: Path, timeout: int) -> tuple[str, float, list]:
    t0 = time.monotonic()
    try:
        p = subprocess.run([QUOD, "check", str(path), "--json"], capture_output=True, text=True,
                           encoding="utf-8", errors="replace", timeout=timeout)
    except subprocess.TimeoutExpired:
        return "hung", time.monotonic() - t0, []
    secs = time.monotonic() - t0
    try:
        diags = json.loads(p.stdout) if p.stdout.strip() else []
    except json.JSONDecodeError:
        diags = []
    errors = [d for d in diags if d.get("severity") == "error"]
    if p.returncode == 0:
        verdict = "survived"
    elif any(d.get("kind") in ("syntax", "type") for d in errors):
        verdict = "invalid"
    elif any(d.get("witness") or (d.get("counterexample") and d.get("evidence") != "unconfirmed") for d in errors):
        verdict = "refuted"
    elif any(d.get("counterexample") for d in errors):
        verdict = "unconfirmed"  # a counterexample the solver or a run could not confirm
    else:
        verdict = "no hint"
    return verdict, secs, errors


def name(f: Path) -> str:
    """quod/rle_encode/solution.quod -> rle_encode; review/isqrt.quod -> isqrt."""
    return f.parent.name if f.stem == "solution" else f.stem


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+", type=Path)
    ap.add_argument("--max", type=int, default=15, help="mutants per file (a seeded sample)")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--timeout", type=int, default=900, help="seconds before a check counts as hung")
    ap.add_argument("--resume", action="store_true", help="keep the rows already in --out, run the rest")
    a = ap.parse_args()
    rnd = random.Random(20261101)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    work = a.out.with_suffix("")
    work.mkdir(parents=True, exist_ok=True)
    rows = []
    if a.resume and a.out.exists():
        rows = [json.loads(line) for line in a.out.read_text(encoding="utf-8").splitlines() if line.strip()]
    done = {(r["file"], r["mutant"]) for r in rows}
    with a.out.open("a" if a.resume else "w", encoding="utf-8") as fh:
        for f in a.files:
            all_m = mutants(f.read_text(encoding="utf-8"))
            sample = rnd.sample(all_m, min(a.max, len(all_m)))  # drawn even when resuming: same sample
            for k, (desc, src) in enumerate(sample):
                if (str(f), desc) in done:
                    continue
                mpath = work / f"{name(f)}_{k}.quod"
                mpath.write_text(src, encoding="utf-8")
                verdict, secs, errors = check(mpath, a.timeout)
                row = {"file": str(f), "mutant": desc, "verdict": verdict, "secs": round(secs, 2),
                       "errors": [{"property": e.get("property"), "evidence": e.get("evidence"),
                                  "message": e.get("message", "")[:160]} for e in errors]}
                rows.append(row)
                fh.write(json.dumps(row) + "\n")
                fh.flush()
                print(f"{verdict:9} {secs:6.1f}s  {name(f)}: {desc}", flush=True)
    invalid = sum(r["verdict"] == "invalid" for r in rows)
    rows = [r for r in rows if r["verdict"] != "invalid"]
    killed = [r for r in rows if r["verdict"] != "survived"]
    print(f"\n{len(rows)} mutants ({invalid} invalid ones left out): {sum(r['verdict'] == 'refuted' for r in rows)} refuted with a counterexample, "
          f"{sum(r['verdict'] == 'unconfirmed' for r in rows)} with an unconfirmed counterexample, "
          f"{sum(r['verdict'] == 'no hint' for r in rows)} rejected without a hint, "
          f"{sum(r['verdict'] == 'survived' for r in rows)} survived, "
          f"{sum(r['verdict'] == 'hung' for r in rows)} hung")
    if killed:
        print(f"time to reject: median {statistics.median(r['secs'] for r in killed):.1f}s, "
              f"max {max(r['secs'] for r in killed):.1f}s")


if __name__ == "__main__":
    main()
