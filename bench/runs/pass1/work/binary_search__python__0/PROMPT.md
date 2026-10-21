Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Given a list of integers `xs` sorted in non-decreasing order (duplicates allowed, possibly empty) and an integer `target`, return an index `i` such that `xs[i] == target`, or -1 if `target` does not occur in `xs`. Must run in O(log n).

## Required signature
```python
def binary_search(xs: list[int], target: int) -> int
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
