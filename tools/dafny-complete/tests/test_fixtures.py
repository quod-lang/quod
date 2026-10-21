"""Expected verdicts on hand-written fixtures covering real-file layout traps.

    python tests/test_fixtures.py
"""
from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "src"))
from dafny_complete.check import Checker  # noqa: E402

EXPECTED = {
    "tricky.dfy": {
        "Main": "skipped", "Abs": "determined", "WeakAbs": "underspecified",
        "Pair": "underspecified", "Clamp": "underspecified", "Inc": "skipped",
        "Length": "determined", "Single": "determined", "Abstract": "inconclusive",
        "NoOut": "skipped", "Copy": "determined", "Bang": "underspecified",
    },
    "arrays.dfy": {
        "KthElement": "determined", "WeakMax": "underspecified",
        "CopyOf": "determined", "Doubled": "underspecified",
    },
}


def main() -> int:
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for name, want in EXPECTED.items():
            dst = Path(tmp) / name
            shutil.copy(HERE / "fixtures" / name, dst)
            got = {r.method: r for r in Checker(dst).run()}
            for method, status in want.items():
                r = got.get(method)
                good = r is not None and r.status == status
                ok &= good
                detail = (r.witness if r and r.witness else (r.reason if r else "NOT FOUND"))
                print(f"{'OK ' if good else 'BAD'} {name}:{method:10} want {status:15} "
                      f"got {(r.status if r else '-'):15} {str(detail)[:80]}")
            for extra in set(got) - set(want):
                ok = False
                print(f"BAD {name}: unexpected method {extra}")
    print("\nfixtures:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
