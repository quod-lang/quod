# T7: the held-out tasks

Protocol: [heldout.md](../../heldout.md). Haiku (`claude-haiku-5-5`), 72 runs on Quod v0.1.6 (`e4d8c13`), Dafny 4.11.0, 2026-11-04 and 05. No run stopped on a usage limit, no restart. `results.jsonl` is as recorded; everything corrected below is corrected here, not there.

## Result

**The measure could not separate the arms: no accepted contract, in any arm, was found unsound.** With a base rate of zero there is nothing to compare, so this says nothing either way on whether checking completeness during writing improves soundness. With 0 unsound of 17 in an arm, a rate of up to about 18% cannot be excluded for that arm, and only for what the pool of wrong results can detect. It shows that this model wrote mostly sound contracts on these six tasks, not that the check is useless elsewhere.

| Arm | Accepted | Sound, by execution | Undecided | Unsound | Judged adequate, of the undecided | Exact | Determined by the tool | Median time | Median cost |
|---|---|---|---|---|---|---|---|---|---|
| `quod` | 17/18 | 17 | 0 | 0 | - | 16 | 15 of 17 | 71 s | 0.017 USD |
| `quod-mcp` | 16/18 | 16 | 0 | 0 | - | 16 | 11 of 16 | 48 s | 0.013 USD |
| `dafny` | 18/18 | 12 | 6 | 0 | 6 of 6 | 12 | 4 of 18 | 33 s | 0.009 USD |
| `dafny-loop` | 18/18 | 13 | 5 | 0 | 5 of 5 | 13 | 8 of 18 | 35 s | 0.008 USD |

"Determined" counts a declared and witnessed `loose` for Quod. For Dafny, it is dafny-complete afterwards, on the required method ([dafny-complete.jsonl](dafny-complete.jsonl)).

**Main comparison, `dafny-loop` against `dafny`:** 13 against 12 sound, a gap of 1 of 18, on one task. The threshold was 4 of 18 over 3 tasks, so the protocol reports no difference. **Read that as no measurable contrast, not as a shown absence of effect:** for these arms, the count mostly says which contracts had every question answered by the tool, not which were sound. The judge's 18 against 18 means little, since it was not calibrated on known wrong contracts. Time and cost did not double.

**What the check did change:** contracts dafny-complete determines rise from 4 to 8 of 18, of which `gcd` from 0 to 3. The agent wrote what the tool can decide, without a measured gain in what the contract excludes.

**Secondary, described only:** all undecided contracts are Dafny ones, on `gcd` and `next_permutation`, the asymmetry the protocol announced. A Quod contract runs on every question, by construction, since its quantifiers are bounded: this is a design choice, not a result of the bench. Dafny's quantifiers over all integers or sequences do not run. The Quod arms took about twice the median time and cost of the Dafny ones. One Quod contract is sound but not exact (`two_sum_sorted`, `quod` #2): it fixes the pair where the task allows any, the over-specification seen on `binary_search`.

## Faults found while measuring

**1. The compiler hangs, at random, on the same file.** Three of the six Quod `transpose` runs hit a `timeout` of the bench's 600 s (the check or the build); the same file usually answers in 3 to 6 s. Rerun 8 times on each of the six files (`check` and `build`, limit 45 s), 12 of 48 commands went over the limit, on 5 of the 6 files. In one rerun a z3 left behind had reached 23 GB of memory, after `quod` was killed. A trace caught the cause afterwards: `(get-value)` on the partial model left by a check that timed out, which has no time limit in z3. Where that check stops depends on timing, hence the randomness. This is a bug of 0.1.6, not of the agent; 0.1.7 limits that read, and 0.1.8 no longer makes it after a check that timed out.

- `transpose`, `quod` #1 and `quod-mcp` #1 are recorded **not accepted** because of it. Measured since, both are exact (see below).
- One run took 1348 s, most of it probably in this hang.

**2. Both recorded escaped bugs are false.**

- `transpose`, `quod-mcp` #2: the build hung, so the hidden tests never ran, and the bench's score counts that as an escape.
- `gcd`, `dafny-loop` #2: the hidden tests matched the method on a normalized name, and took the helper `Gcd` instead of `gcd`. With the exact name ([hidden.py](../../verifbench/hidden.py)), 513 of 513. It is the only Dafny run of T7 with two such names.

All six `transpose` solutions pass 506 of 506 when built outside the hang. **Corrected, no escaped bug in any arm.** The third refusal, `gcd`, `quod-mcp` #2, has nothing to do with the hang: `--require-contracts` refuses it, with the witness `a = 1, b = -1` and the results 1 and 0. **That contract is unsound:** it accepts 0 for `gcd(1, -1)`, and the recomputed measure below confirms it, with `gcd(0, 5) = 0`. The check stopped it, and being refused, it does not count among the accepted. Any comparison of Quod with Dafny must count "unsound or refused as underspecified" together, or a refusal hides the failure. It is also the one direct trace in this suite of the check doing its job, once.

**3. The pool of wrong results was weaker than the self-check.** It contains no result of 4 of the 11 known wrong solutions, on its 14 inputs per task: "a separator joins the fold before it", "ties by engine index", "a copy", "strict comparisons". So a post hoc measure, not in the protocol, ran the same contracts on 3 inputs where each wrong solution is wrong ([adequacy-extended.jsonl](adequacy-extended.jsonl)): **still no contract unsound**; 4 Dafny contracts per arm stay undecided, all but two on `next_permutation`.

## The measure recomputed, outside the protocol

A review of these results found faults in the measure itself, so it was run again ([adequacy-v2.jsonl](adequacy-v2.jsonl), same contracts, no new run of an agent). The main figures above stay as the protocol defined them. Four changes:

- an unknown on a result the task *allows* no longer makes a contract undecided: it says nothing of soundness, only of exactness;
- the pool of wrong results is no longer cut at 8 per input. That cut left out `[-1, -1]` on 4 of the 8 inputs of `two_sum_sorted` that have a pair, the classic weak contract;
- 60 s per proof of a Dafny question instead of 10;
- the solutions that were not accepted are measured too.

| Arm | Submitted | Accepted | Accepted: sound | Undecided | Unsound | Not accepted: unsound | Not accepted: exact |
|---|---|---|---|---|---|---|---|
| `quod` | 18 | 17 | 17 | 0 | 0 | 0 | 1 |
| `quod-mcp` | 18 | 16 | 16 | 0 | 0 | 1 | 1 |
| `dafny` | 18 | 18 | 12 | 6 | 0 | - | - |
| `dafny-loop` | 18 | 18 | 14 | 4 | 0 | - | - |

**The conclusion holds:** a larger pool finds no unsound accepted contract, and the main comparison is 14 against 12, still under the threshold. One contract moves, a `next_permutation` of `dafny-loop`, and because of the corrected count: its only unknowns were on allowed results. The longer limit decided none: the other 10 undecided stay so at 60 s, so their cause is less the time limit than quantifiers over all integers or sequences.

**Not done:** the judge is still not calibrated on known wrong contracts, the evaluator behind `quod contract` has no independent check, and the runs carry no timestamps. The pool is still written by the side under test.

## A later finding: false "unsat" in the compiler

Testing the fix of the hang found another fault, present in these runs' compiler family: after a check stopped by its time limit, z3 can later answer "unsat" to a satisfiable question. On the `transpose` files, 0.1.7 gave 3 false refusals and 1 internal error in 1000 builds, and 0.1.8, which replaces z3 after each timeout, none in 1500 ([notes](../../../docs/releases/v0.1.8.md)). The cause is not isolated inside z3.

These runs used 0.1.6, which was not tested for this. It could have turned a verdict either way, without any sign in `results.jsonl`, though we saw no false proof. **Contracts were measured without z3**, by evaluation or by Dafny, so the soundness figures do not rest on it. Every accepted Quod solution that was built passes its hidden tests. The acceptance and "determined" figures of the Quod arms do rest on it, and were not rerun, since the protocol freezes the compiler.

## Predictions, right or wrong

| Task | Prediction | Outcome |
|---|---|---|
| `gcd` | At most 1 sound by properties in any arm | Right in Quod. Wrong in Dafny according to the judge: 3 by properties. By execution they are undecided |
| `gcd` | At least 2 sound by a model in the Quod arms | **Right** (2, 2) |
| `split_folds` | At least 2 sound in each arm | **Right** (3 each) |
| `split_folds` | At most 1 decided by the tool | **Wrong** in 3 arms of 4 (3, 2, 1, 2) |
| `arbitrate_field` | At least 2 sound in each arm; at least 2 decided in Quod | **Right** (3 each; 3, 3) |
| `transpose` | 3 sound in each arm | **Wrong** in the Quod arms (2 each, because of the hang); right in Dafny |
| `transpose` | At least 2 decided | **Wrong** everywhere (1, 0, 0, 0) |
| `next_permutation` | At most 1 sound by properties in any arm | Right in `quod`, **wrong** in `quod-mcp` (2). Dafny undecided, judged adequate |
| `two_sum_sorted` | At least 2 sound in each arm; at least 2 exact in Quod | **Right** |
| `two_sum_sorted` | At most 1 exact in `dafny`, which cannot declare the freedom | **Wrong:** 3 exact. A contract can simply allow every pair that sums to the target |

The predictions underrated both the agent and what `ensures` can say, and overrated the tools on nested sequences.

## Sensitivity

Every wrong solution fails hidden tests (`python -m verifbench.tasks_heldout`, no problem): gcd negative 276/513; split_folds 137, 244, 179/511; arbitrate_field 458, 449, 430, 132/509; transpose 8/506; next_permutation 371/512; two_sum_sorted 423/510. See fault 3 for the pool.

## Limits

A finite test finds wrong results, it does not exclude them. Six small tasks and one model, whose family also supplies the judge, which answered "adequate" 11 times of 11 and may simply miss faults. The suite has now been read: it is spent. A sample of 5 contracts per arm is in [contracts-to-read.md](contracts-to-read.md).
