Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Normalize a Unix-style path string. Split it on `/`; drop empty components and `.`. A `..` removes the preceding kept component if there is one and it is not itself `..`; otherwise, in an absolute path (one starting with `/`) the `..` is dropped (you cannot go above the root), and in a relative path it is kept. Any other component (including `...` or `.a`) is an ordinary name. An absolute result is `/` followed by the kept components joined with `/` (just `/` if none); a relative result is the kept components joined with `/`, or `.` if none. Never a trailing `/` except for the root.

## Required signature (add the contracts yourself)
```dafny
method normalize_path(p: string) returns (r: string)
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
