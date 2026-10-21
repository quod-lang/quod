Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Simulate an LRU cache with fixed `capacity` (>= 1), initially empty, over `ops`, a list of triples `(kind, key, value)`. kind 0 = get(key): append the cached value to the output, or -1 if absent (value field ignored). kind 1 = put(key, value): store the value (replacing any previous one). Both a successful get and any put make the key the most recently used. When a put inserts a NEW key while the cache already holds `capacity` keys, first evict the least recently used key. Values are >= 0. Return the output list.

## Required signature (add the contracts yourself)
```dafny
method lru_cache(capacity: int, ops: seq<(int, int, int)>) returns (out: seq<int>)
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result.
  Add loop invariants and `decreases` clauses as needed.
- The file must verify: `dafny verify solution.dfy`. Run commands directly in the current directory (no `cd`, no chained commands).
- Forbidden: `assume`, `{:axiom}`, `{:verify false}`, `{:extern}`, and bodiless
  methods, functions or lemmas. Helper functions, predicates and lemmas are allowed.
- When it verifies and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
