Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Rotate a list to the right by `k` positions and return the new list (e.g. [1,2,3] with k=1 -> [3,1,2]). `k` may be any integer: negative values rotate left, values larger than the length wrap around. An empty list returns an empty list.

## Required signature (add the contracts yourself)
```dafny
method rotate(xs: seq<int>, k: int) returns (r: seq<int>)
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
