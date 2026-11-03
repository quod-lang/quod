Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its tools are available to you as MCP tools:
`quod_reference` (the language reference: it is all there is to know about Quod), `quod_check`,
`quod_run` and `quod_build`. There is no shell.

## Specification
Given a list of integers `xs` sorted in non-decreasing order (duplicates allowed, possibly empty) and an integer `target`, return an index `i` such that `xs[i] == target`, or -1 if `target` does not occur in `xs`. Must run in O(log n).

## Required signature (add the contracts yourself)
```rust
fn binary_search(xs: seq<int>, target: int) -> int
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod_check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- `solution.quod` must pass `quod_check` (call it with `path: "solution.quod"`).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
