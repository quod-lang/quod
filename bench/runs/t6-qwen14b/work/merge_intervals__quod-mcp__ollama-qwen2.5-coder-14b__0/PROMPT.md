Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its tools are available to you as MCP tools:
`quod_reference` (the language reference: it is all there is to know about Quod), `quod_check`,
`quod_run` and `quod_build`. There is no shell.

## Specification
Given a list of closed integer intervals `(a, b)` with `a <= b`, in any order (possibly empty, possibly with duplicates), return the union as a list of disjoint intervals sorted by start. Two intervals are merged when they overlap or touch at an endpoint (e.g. (1,3) and (3,5) -> (1,5)); (1,2) and (3,4) are NOT merged.

## Required signature (add the contracts yourself)
```rust
fn merge_intervals(iv: seq<(int, int)>) -> seq<(int, int)>
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod_check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- `solution.quod` must pass `quod_check` (call it with `path: "solution.quod"`).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
