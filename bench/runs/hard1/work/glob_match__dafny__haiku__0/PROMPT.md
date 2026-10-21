Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Return True iff the whole string `text` matches the glob `pattern`. In the pattern, `?` matches exactly one character, `*` matches any sequence of characters (including the empty one), and a backslash `\` makes the following character match literally (so `\*` matches only `*`, `\\` matches only `\`); a lone backslash at the very end of the pattern matches a literal backslash. Every other character matches itself.

## Required signature (add the contracts yourself)
```dafny
method glob_match(pattern: string, text: string) returns (b: bool)
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
