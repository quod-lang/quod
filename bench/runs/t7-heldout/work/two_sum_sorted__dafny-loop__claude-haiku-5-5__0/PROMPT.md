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
  and `ensures` clauses that fully capture the specified result: `dafny-complete solution.dfy` reports a
  contract that accepts two different results for the same input (`[UNDER]`, with a witness). Fix it,
  unless that freedom is what the specification allows.
  Add loop invariants and `decreases` clauses as needed.
- The file must verify: `dafny verify solution.dfy`, and `dafny-complete solution.dfy` must report no
  `[UNDER]` that the specification does not allow. An undecided verdict is acceptable. Run commands directly in the current directory (no `cd`, no chained commands).
- Forbidden: `assume`, `{:axiom}`, `{:verify false}`, `{:extern}`, and bodiless
  methods, functions or lemmas. Helper functions, predicates and lemmas are allowed.
- When it verifies and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
