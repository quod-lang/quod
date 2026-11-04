Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its tools are available to you as MCP tools:
`quod_reference` (the language reference: it is all there is to know about Quod), `quod_check`,
`quod_run` and `quod_build`. There is no shell.

## Specification
Given the classification of each page of a scanned batch, as a list of integers (0: a continuation page, 1: the first page of a document, 2: a separator sheet), return the folds of the batch, in order, as a list of pairs `(start, end)`: the fold covers the pages `start` to `end - 1`. A fold starts at a page classified 1, or at the first page that is not a separator, at the start of the batch or after a separator. It ends just before the next page classified 1, the next separator, or the end of the batch. Separator sheets belong to no fold, every other page belongs to exactly one, and no fold is empty.

## Required signature (add the contracts yourself)
```rust
fn split_folds(pages: seq<int>) -> seq<(int, int)>
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod_check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- `solution.quod` must pass `quod_check` (call it with `path: "solution.quod"`).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
