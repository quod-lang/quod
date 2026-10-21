Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Given a list of integers each in 0..255 (a byte string), return True iff it is well-formed UTF-8 as defined by RFC 3629 / the Unicode standard: every character uses its shortest encoding (no overlong forms), no code point exceeds U+10FFFF, no surrogate code points U+D800..U+DFFF are encoded, and no sequence is truncated or has an invalid continuation byte. The empty list is valid.

## Required signature (add the contracts yourself)
```dafny
method utf8_valid(bs: seq<int>) returns (b: bool)
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
