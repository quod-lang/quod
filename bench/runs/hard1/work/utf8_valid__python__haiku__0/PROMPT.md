Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Given a list of integers each in 0..255 (a byte string), return True iff it is well-formed UTF-8 as defined by RFC 3629 / the Unicode standard: every character uses its shortest encoding (no overlong forms), no code point exceeds U+10FFFF, no surrogate code points U+D800..U+DFFF are encoded, and no sequence is truncated or has an invalid continuation byte. The empty list is valid.

## Required signature
```python
def utf8_valid(bs: list[int]) -> bool
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
