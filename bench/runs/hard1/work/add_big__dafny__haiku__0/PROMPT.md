Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
`a` and `b` are arbitrarily large integers written in canonical decimal form: either `0`, or an optional `-` followed by digits with a non-zero first digit (so no leading zeros, no `+`, no `-0`). Return a + b in the same canonical form. The operands can have hundreds of digits: do not rely on fixed-width integer types.

## Required signature (add the contracts yourself)
```dafny
method add_big(a: string, b: string) returns (s: string)
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
