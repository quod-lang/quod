Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Run-length encode a list of integers: return a list of `(value, count)` pairs, one per maximal run of equal consecutive values, in order. Counts are >= 1. Empty input gives empty output.

## Required signature
```python
def rle_encode(xs: list[int]) -> list[tuple[int, int]]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
