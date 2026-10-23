Implement the function below in Quod, in the file `solution.quod` in the current directory.

Quod is a new verified programming language. Its reference is in `QUOD.md`, in the current
directory: it is all there is to know about Quod (there are no other documents or examples).

## Specification
Simulate a FIFO queue with fixed `capacity` (>= 1), initially empty, over a list of operations `ops` (all >= 0). An op `x > 0` pushes `x`; if the queue is already full, the oldest element is dropped first. An op `0` pops the oldest element and appends it to the output, or appends -1 if the queue is empty. Return the output list.

## Required signature (add the contracts yourself)
```rust
fn bounded_queue(capacity: int, ops: seq<int>) -> seq<int>
```

## Rules
- Add `requires` clauses expressing ONLY the input guarantees stated in the specification,
  and `ensures` clauses that fully capture the specified result: `quod check` rejects a contract
  that accepts two different results for the same input, unless that freedom is intended and
  declared with `loose`. Add loop invariants, `decreases` clauses and helper functions as needed.
- The file must pass `quod check solution.quod`. Run commands directly in the current directory (no `cd`, no chained commands).
- When it passes and you are confident it is correct, stop.
  It will be compiled to Python (`quod build`) and evaluated against hidden tests.
