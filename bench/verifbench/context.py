"""Does a verdict depend on the rest of the file? Each mutant of a program is checked twice: alone,
and followed by an unrelated verified program (on sequences, whose axioms are quantified).

    python -m verifbench.context runs/mutants-0.1.1 --prefix isqrt_ --neighbour quod/rotate/solution.quod --out runs/context.jsonl
"""
from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

from verifbench.mutants import check


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("mutants", type=Path, help="a directory of mutated programs (written by mutants.py)")
    ap.add_argument("--prefix", required=True, help="the mutants to take, e.g. isqrt_")
    ap.add_argument("--neighbour", type=Path, required=True)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    neighbour = a.neighbour.read_text(encoding="utf-8")
    rows = []
    with tempfile.TemporaryDirectory() as tmp, a.out.open("w", encoding="utf-8") as fh:
        for m in sorted(a.mutants.glob(a.prefix + "*.quod")):
            src = m.read_text(encoding="utf-8")
            together = Path(tmp) / m.name
            together.write_text(src + "\n" + neighbour, encoding="utf-8")
            alone_v, alone_s, _ = check(m, a.timeout)
            with_v, with_s, _ = check(together, a.timeout)
            row = {"mutant": m.name, "alone": alone_v, "alone_secs": round(alone_s, 2),
                   "with_neighbour": with_v, "with_secs": round(with_s, 2)}
            rows.append(row)
            fh.write(json.dumps(row) + "\n")
            print(f"{m.name:22} alone {alone_v:9} {alone_s:6.1f}s   with neighbour {with_v:9} {with_s:6.1f}s", flush=True)
    same = sum(r["alone"] == r["with_neighbour"] for r in rows)
    print(f"\n{len(rows)} mutants: same verdict alone and with the neighbour for {same}")


if __name__ == "__main__":
    main()
