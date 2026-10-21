Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Parse a string as a signed 32-bit decimal integer. A valid string is an optional single sign (`+` or `-`) followed by one or more ASCII digits `0`-`9` and nothing else (no whitespace, no other characters; leading zeros are allowed). The value must lie in [-2147483648, 2147483647]. Return `(True, value)` if valid, otherwise `(False, 0)`.

## Required signature (add the contracts yourself)
```dafny
method parse_int(s: string) returns (ok: bool, v: int)
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
