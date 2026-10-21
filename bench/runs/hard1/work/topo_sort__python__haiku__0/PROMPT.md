Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Given `n` >= 1 nodes numbered 0..n-1 and a list of directed edges `(u, v)` (0 <= u, v < n) meaning u must come before v — the list may contain duplicate edges and self-loops — return the lexicographically smallest ordering of all n nodes that respects every edge. If no such ordering exists (the graph has a cycle, including a self-loop), return the empty list.

## Required signature
```python
def topo_sort(n: int, edges: list[tuple[int, int]]) -> list[int]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
