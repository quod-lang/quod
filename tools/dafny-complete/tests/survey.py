"""Static survey of a Dafny corpus: which methods could dafny-complete check, and why not.

    python tests/survey.py <folder> [<folder> ...]
"""
from __future__ import annotations

import collections
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "src"))
from dafny_complete import values as V  # noqa: E402
from dafny_complete.parse import find_methods  # noqa: E402


def classify(m) -> str:
    if not m.outs:
        return "skip: no outputs"
    if not m.ensures:
        return "skip: no ensures"
    if m.in_type and not m.static:
        return "skip: instance method"
    if m.other_clauses:
        return "skip: modifies/reads"
    if any(re.search(r"\b(old|fresh|unchanged|allocated)\s*\(", e) for e in m.ensures):
        return "skip: old/fresh in ensures"
    types = [t for _, t in m.params + m.outs]
    if any(re.search(r"\barray\d*\s*<", t) for t in types):
        return "checkable, uses arrays (no witness yet)"
    if all(V.supported(t) for t in types):
        return "checkable, witness-capable types"
    return "checkable, other types (no witness)"


def main() -> None:
    for folder in map(Path, sys.argv[1:]):
        counts: collections.Counter[str] = collections.Counter()
        files = errors = 0
        for f in sorted(folder.rglob("*.dfy")):
            files += 1
            try:
                ms = find_methods(f.read_text(encoding="utf-8", errors="replace"))
            except Exception:  # noqa: BLE001 - a parser crash is a finding
                errors += 1
                continue
            counts.update(classify(m) for m in ms)
        total = sum(counts.values())
        print(f"\n{folder.name}: {files} files, {total} methods, parser crashes on {errors} files")
        for k, n in counts.most_common():
            print(f"  {n:5}  {100 * n / max(total, 1):5.1f}%  {k}")


if __name__ == "__main__":
    main()
