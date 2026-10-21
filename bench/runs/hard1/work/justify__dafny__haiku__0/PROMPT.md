Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Fully justify text. `words` is a list of non-empty words (no spaces), each of length <= `width`. Greedily pack as many words as possible on each line with at least one space between words, so that each line has exactly `width` characters. On every line except the last, if the line has two or more words, distribute the spaces as evenly as possible between words, giving the extra spaces to the leftmost gaps. A line with a single word, and the last line, are left-justified: words separated by one space, padded with spaces on the right up to `width`. Return the list of lines (empty list for no words).

## Required signature (add the contracts yourself)
```dafny
method justify(words: seq<string>, width: int) returns (lines: seq<string>)
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
