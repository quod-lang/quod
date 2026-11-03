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

A smaller model, Haiku, one trial per task, twice: [quod2-haiku](../runs/quod2-haiku) with the
compiler of the time, then [quod3-haiku](../runs/quod3-haiku) after the external review (lemmas,
counterexamples by execution, contract notes) and a longer language reference.

| Task | quod2-haiku | quod3-haiku |
|---|---|---|
| binary_search | verified, completeness not decided | verified, determined, 71 s |
| merge_intervals | verified, not decided | verified, not decided, 28 min |
| rle_encode | verified **without any ensures** (time limit hit) | verified, not decided |
| bounded_queue | rejected | verified, determined, 84 s |
| max_subarray | rejected | verified, not decided, 46 s |
| rotate | verified, by a model | verified, determined, by properties |

quod2-haiku found the holes in the completeness check (a `loose` that accepts everything, no
ensures at all), now warnings. In quod3-haiku all six verify and pass the hidden tests, three with
a determined contract, for 0.59 USD instead of 2.83; the agent wrote `lemma` unprompted in four
tasks. One trial each, and two things changed at once (the compiler and the reference): a
direction, not a measure.

Then the same model through the MCP server: [quod4-haiku-mcp](../runs/quod4-haiku-mcp) (the
`quod-mcp` arm: no shell and no QUOD.md, only the files and the four tools of `quod mcp`), with the
same compiler as quod3-haiku.

| | quod3-haiku (shell) | quod4-haiku-mcp (MCP) |
|---|---|---|
| Verified and pass the hidden tests | 6/6 | 6/6 |
| Contract determined | 3/6 | 6/6 (merge_intervals and rle_encode by a model) |
| Turns per task | 7 to 42 | 4 to 16 |
| Time, cost | 47 min, 0.59 USD | 7 min, 0.08 USD |

The agent no longer gropes with a shell, paths and temporary files: it calls `quod_check` and
reads a structured answer. One trial per task again: a direction, not a measure.

### Three trials, Dafny, and another vendor

[t6-haiku](../runs/t6-haiku): Haiku, three trials of the six tasks in each of three arms, with
the 0.1.3 compiler. The Dafny arm is the one of Phase 0 (shell, `dafny verify`); its contracts
were then given to [dafny-complete](../../tools/dafny-complete/)
([results](../runs/t6-haiku/dafny-complete.jsonl)).

| | quod (shell) | quod-mcp | dafny |
|---|---|---|---|
| Accepted by the verifier | 18/18 | 16/18 | 18/18 |
| Pass all the hidden tests | 18/18 | 17/18 | 18/18 |
| Contract determined | 17/18 | 12/18 | 9/18 (dafny-complete) |
| Contract style | 10 properties, 8 model | 12 properties, 6 model | — |
| Time, cost (18 runs) | 54 min, 0.54 USD | 71 min, 1.15 USD | 17 min, 0.24 USD |

- **No escaped bug in any arm**: every accepted solution passes the hidden tests.
- **The MCP advantage of quod4-haiku-mcp does not hold** over three trials. Through MCP the agent
  writes more contracts by properties, which are harder to prove and to determine: two solutions
  are left with inconclusive obligations (merge_intervals, rotate), five contracts with
  inconclusive completeness.
- **Dafny is faster and cheaper**, and its contracts say less. Of the 18, dafny-complete finds 3
  underspecified (all binary_search: any index of a duplicate is accepted, which the task allows;
  Dafny has no `loose` to say so) and cannot decide 6 (merge_intervals, rle_encode). In Quod the
  completeness check is part of acceptance, so the agent keeps working until it is decided.

[t6-qwen14b](../runs/t6-qwen14b): another vendor, Qwen 2.5 Coder 14B run locally through Ollama,
in the `quod-mcp` arm (the agent is [ollama_agent.py](../verifbench/ollama_agent.py), an MCP
client with the same tools), three trials of the six tasks. **0/18**: every run stops at 40
turns, 13 of the 18 final files on a syntax error. Most of these are Dafny habits: contract
clauses in the body, `;` after a clause, `for`, `let result`, `return` in an ensures. The parser
now names each of them and says what to write instead.

[t6-qwen14b-hints](../runs/t6-qwen14b-hints), the same run with those messages: **0/18 again**.
The habits that the messages name almost vanish from the final files (5 clauses in the body
become 0, 3 `let result` become 0), but others take their place (an expression in the middle of a
block, `:` for `in`, `|s|` for `len(s)`), and 3 files still put `;` after a clause. The model fixes
the error it is shown and makes another; 15 of the 18 final files end on a syntax error. A
language that no model has seen needs, for now, a model that can follow a reference it reads for
the first time.

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

**Inputs from the solver.** An external counter-review found the family these runs miss: bugs
whose input must satisfy a quantified `requires`, which random inputs almost never do and the
solver does not find either. [quantified.quod](../mutants/quantified.quod) has three such
functions (at least four strictly increasing values, from 10 up); 30 mutants:

| Compiler | Refuted, with a counterexample | Rejected, no counterexample | Survived | Median time to reject |
|---|---|---|---|---|
| random inputs only ([log](../runs/mutants-quantified-before.log)) | 0 | 29 | 1 | 10.7 s |
| and inputs from the solver ([log](../runs/mutants-quantified-after.log)) | 28 | 1 | 1 | 0.2 s |

When few random inputs satisfy the `requires`, the solver finds some, at a fixed length where
the quantifiers unfold. On the eight programs above ([log](../runs/mutants-solver-inputs.log)),
nothing changes: same verdicts, same time.

**Measured and not adopted: bounded unfolding (fuel).** Dafny unfolds a recursive function a
bounded number of times. Tried with 2 levels ([patch](../runs/fuel-experiment.patch),
[log](../runs/mutants-fuel2.log)), on the same mutants: as many refuted (51 of the 55 still in the
sample), 13% less time in all, and the gain was the completeness check giving up sooner on
rle_encode, with the same verdict. But a correct proof failed: the invariant
`forall i in 0..k: sum(xs, i, k) <= here` of max_subarray, even with 3 levels, because the
unfolded `sum` is a term of a lower level that the quantified invariant does not match. That
also rejected an equivalent mutant. Unbounded unfolding stays.
