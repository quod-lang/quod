"""Run dafny-complete on a corpus of real Dafny files and summarize the verdicts.

    python tests/corpus_run.py <folder> --out results.jsonl [--sample N] [--jobs 4]

Each file is copied to its own temporary folder first (the tool writes its generated files
next to the checked file). One JSON line per method; a summary at the end.
"""
from __future__ import annotations

import argparse
import collections
import json
import random
import shutil
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "src"))
from dafny_complete.check import Checker  # noqa: E402


def check_file(f: Path) -> list[dict]:
    t0 = time.monotonic()
    with tempfile.TemporaryDirectory() as tmp:
        dst = Path(tmp) / f.name
        shutil.copy(f, dst)
        try:
            results = Checker(dst).run()
        except Exception as e:  # noqa: BLE001 - a tool crash is a finding
            return [{"file": f.name, "method": None, "status": "tool_crash",
                     "reason": f"{type(e).__name__}: {e}", "secs": round(time.monotonic() - t0, 1)}]
    secs = round(time.monotonic() - t0, 1)
    return [{"file": f.name, "method": r.method, "line": r.line, "status": r.status,
             "reason": r.reason, "witness": r.witness, "notes": r.notes, "secs": secs}
            for r in results]


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("folder", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--sample", type=int, default=0)
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--jobs", type=int, default=4)
    a = p.parse_args()

    files = sorted(a.folder.rglob("*.dfy"))
    if a.sample:
        files = sorted(random.Random(a.seed).sample(files, min(a.sample, len(files))))
    a.out.parent.mkdir(parents=True, exist_ok=True)
    counts: collections.Counter[str] = collections.Counter()
    t0 = time.monotonic()
    with a.out.open("w", encoding="utf-8") as out, ThreadPoolExecutor(a.jobs) as pool:
        futures = {pool.submit(check_file, f): f for f in files}
        for n, fut in enumerate(as_completed(futures), 1):
            rows = fut.result()
            for r in rows:
                out.write(json.dumps(r, default=repr) + "\n")
                counts[r["status"]] += 1
            out.flush()
            if n % 10 == 0 or n == len(files):
                print(f"[{n}/{len(files)}] {time.monotonic() - t0:.0f}s  " +
                      ", ".join(f"{k} {v}" for k, v in counts.most_common()), flush=True)
    print("done")


if __name__ == "__main__":
    main()
