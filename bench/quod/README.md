# The VerifBench tasks in Quod

[Français](README.fr.md)

The six VerifBench tasks without strings, written in Quod 0.1 by hand (step 6 of
[the 0.1 scope](../../spec/quod-0.1.md)), before asking an agent to write them from the grammar
alone. Each one verifies, compiles to Python, and passes the VerifBench hidden tests (the same
tests as the Python and Dafny arms of Phase 0).

| Task | Lines | Obligations | Contract determined | Hints | Hidden tests |
|---|---|---|---|---|---|
| [binary_search](binary_search/solution.quod) | 22 | 29 | ✅ (with `loose`) | none | 510/510 |
| [merge_intervals](merge_intervals/solution.quod) | 87 | 168 | ⚠️ not decided | 6 asserts, 2 lemmas | 508/508 |
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

## An agent writes them

Run [quod1](../runs/quod1): the default model of Claude Code, one trial per task, with only the
[language reference](../runs/quod1/work/rotate__quod__default__0/QUOD.md) (the language part of
the 0.1 scope, without its example) and the task's specification.

| Task | Time | Turns | Contract style | Hidden tests |
|---|---|---|---|---|
| binary_search | 26 s | 6 | properties, `loose` found by the agent | 510/510 |
| merge_intervals | 18 min | 26 | model (recursive insertion) | 508/508 |
| rle_encode | 25 s | 4 | model (recursive encoding) | 506/506 |
| bounded_queue | 23 s | 4 | model (the queue, step by step) | 505/505 |
| max_subarray | 48 s | 7 | properties | 506/506 |
| rotate | 17 s | 4 | restated (the ensures is the body) | 508/508 |

All six verify and pass the hidden tests (about 1.70 USD in all). No weak contract got through:
the completeness check rejects them. But the shortest determined contract is
`result == <the body>`, or `result == f(...)` for a recursive `f` that computes the same thing:
four of six contracts say how to compute the result, not what it is. Hence the
[contract style](../../spec/quod-0.1.md#contract-style) that `quod check` now reports, with a
warning for a restated body.

## What writing them changed in the verifier

- **Sequences are axiomatized** (as Dafny does), instead of using Z3's sequence theory, which
  did not carry quantified facts over `r[..n] + [x]` and made proofs unstable.
- **Loop bodies are checked without the facts about the variables' values before the loop**,
  which misled Z3 (a timeout became a 0.1 s proof).
- **An obligation that fails in Z3's incremental mode is tried again on a fresh solver**; the two
  modes succeed on different queries.
- Tuple and sequence literals take `nat` parts: `(x, c + 1)` where `(int, nat)` is expected.

And in the way Quod is written: [hints and lemmas](../../spec/quod-0.1.md#hints-and-lemmas).

## Small bugs: a mutant bench

[mutants.py](../verifbench/mutants.py) changes one operator or constant in the code of a verified
program (never in its contracts), and records how `quod check` rejects it: with a counterexample,
without one, or not at all (an equivalent mutant, or a bug the contract does not see). A seeded
sample of 10 mutants per program, over the six solutions above and the two programs of an external
review ([isqrt](../review/isqrt.quod), [prefix_sums](../review/prefix_sums.quod)); 64 valid mutants.

| Compiler | Refuted, with a counterexample | Rejected, no counterexample | Hung | Survived | Median time to reject |
|---|---|---|---|---|---|
| before ([log](../runs/mutants-before.log)) | 7 | 48 | 2 | 7 | 27 s |
| with counterexamples by execution ([log](../runs/mutants-after.log)) | 57 | 0 | 0 | 7 | 1.3 s |

Before asking Z3, the compiler now runs each function on small inputs that satisfy its `requires`,
checking every obligation on the way: a broken one is a certain counterexample, found in
milliseconds where Z3 often timed out. The two hung checks were Z3 not keeping its own time limit
(over 15 minutes); a watchdog now replaces the process. The 7 survivors are all equivalent
mutants (`>=` for `>` where both branches agree, a model function's value on an empty input, a
lemma stopping one step later...).

**Measured and not adopted: bounded unfolding (fuel).** Dafny unfolds a recursive function a
bounded number of times. Tried with 2 levels ([patch](../runs/fuel-experiment.patch),
[log](../runs/mutants-fuel2.log)), on the same mutants: as many refuted (51 of the 55 still in the
sample), 13% less time in all, and the gain was the completeness check giving up sooner on
rle_encode, with the same verdict. But a correct proof failed: the invariant
`forall i in 0..k: sum(xs, i, k) <= here` of max_subarray, even with 3 levels, because the
unfolded `sum` is a term of a lower level that the quantified invariant does not match. That
also rejected an equivalent mutant. Unbounded unfolding stays.
