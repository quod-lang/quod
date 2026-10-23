# The VerifBench tasks in Quod

[Français](README.fr.md)

The six VerifBench tasks without strings, written in Quod 0.1 by hand (step 6 of
[the 0.1 scope](../../spec/quod-0.1.md)), before asking an agent to write them from the grammar
alone. Each one verifies, compiles to Python, and passes the VerifBench hidden tests (the same
tests as the Python and Dafny arms of Phase 0).

| Task | Lines | Obligations | Contract determined | Hints | Hidden tests |
|---|---|---|---|---|---|
| [binary_search](binary_search/solution.quod) | 22 | 29 | ✅ (with `loose`) | none | 510/510 |
| [merge_intervals](merge_intervals/solution.quod) | 89 | 176 | ⚠️ not decided | 6 asserts, 2 lemmas | 508/508 |
| [rle_encode](rle_encode/solution.quod) | 39 | 55 | ⚠️ not decided | none | 506/506 |
| [bounded_queue](bounded_queue/solution.quod) | 49 | 69 | ✅ | 3 asserts | 505/505 |
| [max_subarray](max_subarray/solution.quod) | 31 | 64 | ✅ | none | 506/506 |
| [rotate](rotate/solution.quod) | 6 | 10 | ✅ | none | 508/508 |

Lines exclude comments and blank lines. The two ⚠️ are canonical forms (a run-length encoding,
a list of disjoint sorted intervals): their uniqueness needs an induction, and the check says
"not decided" (a warning) rather than guessing. In Phase 0, our completeness check of the Dafny
solutions ([dafny-complete](../../tools/dafny-complete)) gave the same false alarm on these two tasks. For comparison, the Dafny solution Opus wrote for merge_intervals is 193
lines.

To run one:

```bash
quod build bench/quod/rotate/solution.quod -o out/rotate
cd bench
python -m verifbench.hidden --task rotate --arm python --dir ../out/rotate
```

## What writing them changed in the verifier

- **Sequences are axiomatized** (as Dafny does), instead of using Z3's sequence theory, which
  did not carry quantified facts over `r[..n] + [x]` and made proofs unstable.
- **Loop bodies are checked without the facts about the variables' values before the loop**,
  which misled Z3 (a timeout became a 0.1 s proof).
- **An obligation that fails in Z3's incremental mode is tried again on a fresh solver**; the two
  modes succeed on different queries.
- Tuple and sequence literals take `nat` parts: `(x, c + 1)` where `(int, nat)` is expected.

And in the way Quod is written: [hints and lemmas](../../spec/quod-0.1.md#hints-and-lemmas).
