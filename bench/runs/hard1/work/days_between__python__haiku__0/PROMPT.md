Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Given two valid dates (y1, m1, d1) and (y2, m2, d2) in the proleptic Gregorian calendar with years 1 to 9999, return the number of days from the first date to the second (negative if the second date is earlier, 0 if equal). A year is a leap year if divisible by 4, except years divisible by 100 that are not divisible by 400.

## Required signature
```python
def days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) -> int
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
