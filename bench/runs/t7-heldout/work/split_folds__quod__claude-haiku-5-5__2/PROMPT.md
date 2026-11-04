Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its reference is in `QUOD.md`, in the current
directory: it is all there is to know about Quod (there are no other documents or examples).

## Specification
Given the classification of each page of a scanned batch, as a list of integers (0: a continuation page, 1: the first page of a document, 2: a separator sheet), return the folds of the batch, in order, as a list of pairs `(start, end)`: the fold covers the pages `start` to `end - 1`. A fold starts at a page classified 1, or at the first page that is not a separator, at the start of the batch or after a separator. It ends just before the next page classified 1, the next separator, or the end of the batch. Separator sheets belong to no fold, every other page belongs to exactly one, and no fold is empty.

## Required signature (add the contracts yourself)
```rust
fn split_folds(pages: seq<int>) -> seq<(int, int)>
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- The file must pass `quod check solution.quod`. Run commands directly in the current directory (no `cd`, no chained commands).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python (`quod build`) and evaluated against hidden tests.
