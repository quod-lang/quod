Implement the method below in Dafny, in the file `solution.dfy` in the current directory,
inside `module Solution { ... }`.

## Specification
Several engines propose a value for the same field. Each candidate is a triple `(engine, confidence, value)`, with `engine` an index into `rank` and `confidence` between 0 and 100; `threshold` is also between 0 and 100. `rank[e]` is the trust order of engine `e`: a smaller rank is more trusted. Return the index, in `candidates`, of the retained candidate: among the candidates whose confidence is at least `threshold`, the one with the highest confidence; between equal confidences, the one whose engine has the smallest rank; and between equal confidences and equal ranks, the first one. If no candidate reaches the threshold, return -1: the field goes to manual validation.

## Required signature (add the contracts yourself)
```dafny
method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `dafny-complete solution.dfy` reports a
  contract that accepts two different results for the same input (`[UNDER]`, with a witness). Fix it,
  unless that freedom is what the specification allows.
  Add loop invariants and `decreases` clauses as needed.
- The file must verify: `dafny verify solution.dfy`, and `dafny-complete solution.dfy` must report no
  `[UNDER]` that the specification does not allow. An undecided verdict is acceptable. Run commands directly in the current directory (no `cd`, no chained commands).
- Forbidden: `assume`, `{:axiom}`, `{:verify false}`, `{:extern}`, and bodiless
  methods, functions or lemmas. Helper functions, predicates and lemmas are allowed.
- When it verifies and you are confident it is correct, stop.
  It will be compiled to Python and evaluated against hidden tests.
