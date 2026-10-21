Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Given two valid dates (y1, m1, d1) and (y2, m2, d2) in the proleptic Gregorian calendar with years 1 to 9999, return the number of days from the first date to the second (negative if the second date is earlier, 0 if equal). A year is a leap year if divisible by 4, except years divisible by 100 that are not divisible by 400.

## Required signature (add the contracts yourself)
```dafny
method days_between(y1: int, m1: int, d1: int, y2: int, m2: int, d2: int) returns (n: int)
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
