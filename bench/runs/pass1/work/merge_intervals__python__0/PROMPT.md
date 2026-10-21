Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Given a list of closed integer intervals `(a, b)` with `a <= b`, in any order (possibly empty, possibly with duplicates), return the union as a list of disjoint intervals sorted by start. Two intervals are merged when they overlap or touch at an endpoint (e.g. (1,3) and (3,5) -> (1,5)); (1,2) and (3,4) are NOT merged.

## Required signature
```python
def merge_intervals(iv: list[tuple[int, int]]) -> list[tuple[int, int]]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
