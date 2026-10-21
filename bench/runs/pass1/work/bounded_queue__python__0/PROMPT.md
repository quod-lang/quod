Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Simulate a FIFO queue with fixed `capacity` (>= 1), initially empty, over a list of operations `ops` (all >= 0). An op `x > 0` pushes `x`; if the queue is already full, the oldest element is dropped first. An op `0` pops the oldest element and appends it to the output, or appends -1 if the queue is empty. Return the output list.

## Required signature
```python
def bounded_queue(capacity: int, ops: list[int]) -> list[int]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
