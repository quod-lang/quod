Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its reference is in `QUOD.md`, in the current
directory: it is all there is to know about Quod (there are no other documents or examples).

## Specification
Several engines propose a value for the same field. Each candidate is a triple `(engine, confidence, value)`, with `engine` an index into `rank` and `confidence` between 0 and 100; `threshold` is also between 0 and 100. `rank[e]` is the trust order of engine `e`: a smaller rank is more trusted. Return the index, in `candidates`, of the retained candidate: among the candidates whose confidence is at least `threshold`, the one with the highest confidence; between equal confidences, the one whose engine has the smallest rank; and between equal confidences and equal ranks, the first one. If no candidate reaches the threshold, return -1: the field goes to manual validation.

## Required signature (add the contracts yourself)
```rust
fn arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) -> int
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- The file must pass `quod check solution.quod`. Run commands directly in the current directory (no `cd`, no chained commands).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python (`quod build`) and evaluated against hidden tests.
