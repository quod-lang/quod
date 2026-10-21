Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
`a` and `b` are arbitrarily large integers written in canonical decimal form: either `0`, or an optional `-` followed by digits with a non-zero first digit (so no leading zeros, no `+`, no `-0`). Return a + b in the same canonical form. The operands can have hundreds of digits: do not rely on fixed-width integer types.

## Required signature
```python
def add_big(a: str, b: str) -> str
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
