Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Parse a string as a signed 32-bit decimal integer. A valid string is an optional single sign (`+` or `-`) followed by one or more ASCII digits `0`-`9` and nothing else (no whitespace, no other characters; leading zeros are allowed). The value must lie in [-2147483648, 2147483647]. Return `(True, value)` if valid, otherwise `(False, 0)`.

## Required signature
```python
def parse_int(s: str) -> tuple[bool, int]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
