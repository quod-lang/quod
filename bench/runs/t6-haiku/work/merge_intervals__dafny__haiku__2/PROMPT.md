Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Given a list of closed integer intervals `(a, b)` with `a <= b`, in any order (possibly empty, possibly with duplicates), return the union as a list of disjoint intervals sorted by start. Two intervals are merged when they overlap or touch at an endpoint (e.g. (1,3) and (3,5) -> (1,5)); (1,2) and (3,4) are NOT merged.

## Required signature (add the contracts yourself)
```dafny
method merge_intervals(iv: seq<(int, int)>) returns (r: seq<(int, int)>)
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
