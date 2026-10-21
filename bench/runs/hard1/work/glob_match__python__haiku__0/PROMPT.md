Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Return True iff the whole string `text` matches the glob `pattern`. In the pattern, `?` matches exactly one character, `*` matches any sequence of characters (including the empty one), and a backslash `\` makes the following character match literally (so `\*` matches only `*`, `\\` matches only `\`); a lone backslash at the very end of the pattern matches a literal backslash. Every other character matches itself.

## Required signature
```python
def glob_match(pattern: str, text: str) -> bool
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
