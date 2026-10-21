Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Simulate an LRU cache with fixed `capacity` (>= 1), initially empty, over `ops`, a list of triples `(kind, key, value)`. kind 0 = get(key): append the cached value to the output, or -1 if absent (value field ignored). kind 1 = put(key, value): store the value (replacing any previous one). Both a successful get and any put make the key the most recently used. When a put inserts a NEW key while the cache already holds `capacity` keys, first evict the least recently used key. Values are >= 0. Return the output list.

## Required signature
```python
def lru_cache(capacity: int, ops: list[tuple[int, int, int]]) -> list[int]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
