Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its reference is in `QUOD.md`, in the current
directory: it is all there is to know about Quod (there are no other documents or examples).

## Specification
Given a list of integers `xs` sorted in non-decreasing order (duplicates allowed, possibly empty) and an integer `target`, return an index `i` such that `xs[i] == target`, or -1 if `target` does not occur in `xs`. Must run in O(log n).

## Required signature (add the contracts yourself)
```rust
fn binary_search(xs: seq<int>, target: int) -> int
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- The file must pass `quod check solution.quod`. Run commands directly in the current directory (no `cd`, no chained commands).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python (`quod build`) and evaluated against hidden tests.
