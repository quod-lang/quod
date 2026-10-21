Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Normalize a Unix-style path string. Split it on `/`; drop empty components and `.`. A `..` removes the preceding kept component if there is one and it is not itself `..`; otherwise, in an absolute path (one starting with `/`) the `..` is dropped (you cannot go above the root), and in a relative path it is kept. Any other component (including `...` or `.a`) is an ordinary name. An absolute result is `/` followed by the kept components joined with `/` (just `/` if none); a relative result is the kept components joined with `/`, or `.` if none. Never a trailing `/` except for the root.

## Required signature
```python
def normalize_path(p: str) -> str
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
