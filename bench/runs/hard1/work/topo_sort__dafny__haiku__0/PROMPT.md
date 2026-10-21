Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Given `n` >= 1 nodes numbered 0..n-1 and a list of directed edges `(u, v)` (0 <= u, v < n) meaning u must come before v — the list may contain duplicate edges and self-loops — return the lexicographically smallest ordering of all n nodes that respects every edge. If no such ordering exists (the graph has a cycle, including a self-loop), return the empty list.

## Required signature (add the contracts yourself)
```dafny
method topo_sort(n: int, edges: seq<(int, int)>) returns (order: seq<int>)
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
