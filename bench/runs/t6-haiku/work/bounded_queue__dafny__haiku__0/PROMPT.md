Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Simulate a FIFO queue with fixed `capacity` (>= 1), initially empty, over a list of operations `ops` (all >= 0). An op `x > 0` pushes `x`; if the queue is already full, the oldest element is dropped first. An op `0` pops the oldest element and appends it to the output, or appends -1 if the queue is empty. Return the output list.

## Required signature (add the contracts yourself)
```dafny
method bounded_queue(capacity: int, ops: seq<int>) returns (out: seq<int>)
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
