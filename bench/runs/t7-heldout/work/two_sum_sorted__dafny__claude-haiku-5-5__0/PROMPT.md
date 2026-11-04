Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and `xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do.

## Required signature (add the contracts yourself)
```dafny
method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
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
