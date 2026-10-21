"""Regression: run dafny-complete on the 24 VerifBench Dafny solutions and compare with the
verdicts established by the bench's own (oracle-based) completeness + witness study.

    python tests/bench_regression.py
"""
from __future__ import annotations

import json
import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "src"))
from dafny_complete.check import Checker  # noqa: E402

BENCH = HERE.parents[2] / "bench"

# Expected verdict per (run, task, model): established in bench/README.md.
UNDER = {("pass1", "binary_search", "default"), ("hard1", "add_big", "haiku"),
         ("hard1", "justify", "haiku"), ("hard1", "lru_cache", "haiku"),
         ("hard1", "normalize_path", "haiku"), ("hard1", "topo_sort", "haiku")}
INCONCLUSIVE = {("pass1", "merge_intervals", "default"), ("pass1", "rle_encode", "default"),
                ("hard1", "add_big", "opus")}


def main() -> int:
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for run in ("pass1", "hard1"):
            for line in (BENCH / "runs" / run / "results.jsonl").read_text(encoding="utf-8").splitlines():
                r = json.loads(line)
                if r["arm"] != "dafny" or not r["accepted"]:
                    continue
                key = (run, r["task"], r.get("model", "default"))
                src = BENCH / "runs" / run / "work" / Path(r["workdir"]).name / "solution.dfy"
                dst = Path(tmp) / f"{run}_{r['task']}_{key[2]}.dfy"
                shutil.copy(src, dst)
                res = [x for x in Checker(dst, only=[r["task"]]).run() if x.method == r["task"]][0]
                want = ("underspecified" if key in UNDER else
                        "inconclusive" if key in INCONCLUSIVE else "determined")
                good = res.status == want
                ok &= good
                w = res.witness
                extra = (f"{w['input']} -> {w['result_a']!r} / {w['result_b']!r}" if w
                         else res.reason[:70])
                print(f"{'OK ' if good else 'BAD'} {run:6} {r['task']:16} {key[2]:8} "
                      f"{res.status:15} {extra}", flush=True)
    print("\nregression:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
