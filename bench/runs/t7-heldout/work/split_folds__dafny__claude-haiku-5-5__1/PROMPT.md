Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Given the classification of each page of a scanned batch, as a list of integers (0: a continuation page, 1: the first page of a document, 2: a separator sheet), return the folds of the batch, in order, as a list of pairs `(start, end)`: the fold covers the pages `start` to `end - 1`. A fold starts at a page classified 1, or at the first page that is not a separator, at the start of the batch or after a separator. It ends just before the next page classified 1, the next separator, or the end of the batch. Separator sheets belong to no fold, every other page belongs to exactly one, and no fold is empty.

## Required signature (add the contracts yourself)
```dafny
method split_folds(pages: seq<int>) returns (r: seq<(int, int)>)
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
