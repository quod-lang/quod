"""Complexity bench of the Python backend: does the generated code keep the complexity of the
Quod program? binary_search should be O(log n) per call, prefix_sums O(n), range_sum O(1).

    python -m verifbench.complexity [--quod PATH] [--out FILE]

Builds examples/binary_search.quod and examples/prefix_sums.quod with the given quod, then times
each function at n = 10^3, 10^4, 10^5 (the best of several runs).
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import timeit
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
QUOD = os.environ.get("QUOD_EXE") or str(ROOT / "artifacts" / "aot" / ("quod.exe" if os.name == "nt" else "quod"))
SIZES = [10**3, 10**4, 10**5]


def build(quod: str, example: str, out: Path):
    subprocess.run([quod, "build", str(ROOT / "examples" / f"{example}.quod"), "-o", str(out)],
                   check=True, capture_output=True)
    spec = importlib.util.spec_from_file_location(example, out / f"{example}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def best(stmt, number: int) -> float:
    """Seconds per call, the best of 5 repeats."""
    return min(timeit.repeat(stmt, number=number, repeat=5)) / number


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quod", default=QUOD)
    ap.add_argument("--out", type=Path, default=None, help="append the rows to this jsonl file")
    ap.add_argument("--label", default=None, help="name of this compiler in the rows (default: its folder)")
    a = ap.parse_args()
    sys.setrecursionlimit(10_000)
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        bs = build(a.quod, "binary_search", Path(tmp))
        ps = build(a.quod, "prefix_sums", Path(tmp))
        for n in SIZES:
            xs = list(range(n))
            table = ps.prefix_sums(xs)
            rows.append({"n": n,
                         "binary_search": best(lambda: bs.binary_search(xs, n // 3), 200),
                         "prefix_sums": best(lambda: ps.prefix_sums(xs), 3),
                         "range_sum": best(lambda: ps.range_sum(xs, table, 0, n), 200)})
    print(f"quod: {a.quod}")
    print(f"{'n':>8} {'binary_search':>15} {'prefix_sums':>15} {'range_sum':>15}")
    for r in rows:
        print(f"{r['n']:>8} " + " ".join(f"{r[k] * 1e6:>12.1f} us" for k in ("binary_search", "prefix_sums", "range_sum")))
    if a.out:
        with a.out.open("a", encoding="utf-8") as fh:
            for r in rows:
                fh.write(json.dumps({"quod": a.label or Path(a.quod).parent.name, **r}) + "\n")


if __name__ == "__main__":
    main()
