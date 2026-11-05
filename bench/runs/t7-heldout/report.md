# T7: the held-out tasks

Protocol: [heldout.md](../../heldout.md). Haiku (`claude-haiku-5-5`), 72 runs on Quod v0.1.6 (`e4d8c13`), Dafny 4.11.0, 2026-11-04 and 05. No run stopped on a usage limit, no restart. `results.jsonl` is as recorded; everything corrected below is corrected here, not there.

## Result

**On these tasks, checking completeness while the agent writes changed nothing measurable in soundness: no accepted contract, in any arm, was found unsound.** The measure hit its ceiling, so it cannot tell the arms apart. It shows the agent did not need the check to write sound contracts here, not that the check is useless elsewhere.

| Arm | Accepted | Sound, by execution | Undecided | Unsound | Judged adequate, of the undecided | Exact | Determined by the tool | Median time | Median cost |
|---|---|---|---|---|---|---|---|---|---|
| `quod` | 17/18 | 17 | 0 | 0 | - | 16 | 15 of 17 | 71 s | 0.017 USD |
| `quod-mcp` | 16/18 | 16 | 0 | 0 | - | 16 | 11 of 16 | 48 s | 0.013 USD |
| `dafny` | 18/18 | 12 | 6 | 0 | 6 of 6 | 12 | 4 of 18 | 33 s | 0.009 USD |
| `dafny-loop` | 18/18 | 13 | 5 | 0 | 5 of 5 | 13 | 8 of 18 | 35 s | 0.008 USD |

"Determined" counts a declared and witnessed `loose` for Quod. For Dafny, it is dafny-complete afterwards, on the required method ([dafny-complete.jsonl](dafny-complete.jsonl)).

**Main comparison, `dafny-loop` against `dafny`:** 13 against 12 sound, a gap of 1 of 18, on one task. The threshold was 4 of 18 over 3 tasks: **no difference.** With the judge, 18 against 18. Time and cost did not double.

**What the check did change:** contracts dafny-complete determines rise from 4 to 8 of 18, of which `gcd` from 0 to 3. The agent wrote what the tool can decide, without a measured gain in what the contract excludes.

**Secondary, described only:** all undecided contracts are Dafny ones, on `gcd` and `next_permutation`, the asymmetry the protocol announced. A Quod contract runs on every question; Dafny's quantifiers over all integers or sequences do not. The Quod arms took about twice the median time and cost of the Dafny ones. One Quod contract is sound but not exact (`two_sum_sorted`, `quod` #2): it fixes the pair where the task allows any, the over-specification seen on `binary_search`.

## Faults found while measuring

**1. The compiler hangs, at random, on the same file.** Three of the six Quod `transpose` runs hit a `timeout` of the bench's 600 s (the check or the build); the same file usually answers in 3 to 6 s. Rerun 8 times on each of the six files (`check` and `build`, limit 45 s), 12 of 48 commands went over the limit, on 5 of the 6 files. In one rerun a z3 left behind had reached 23 GB of memory, after `quod` was killed. A trace caught the cause afterwards: `(get-value)` on the partial model left by a check that timed out, which has no time limit in z3. Where that check stops depends on timing, hence the randomness. This is a bug of 0.1.6, not of the agent; 0.1.7 limits that read.

- `transpose`, `quod` #1 and `quod-mcp` #1 are recorded **not accepted** because of it. Their `ensures` were not measured.
- One run took 1348 s, most of it probably in this hang.

**2. Both recorded escaped bugs are false.**

- `transpose`, `quod-mcp` #2: the build hung, so the hidden tests never ran, and the bench's score counts that as an escape.
- `gcd`, `dafny-loop` #2: the hidden tests matched the method on a normalized name, and took the helper `Gcd` instead of `gcd`. With the exact name ([hidden.py](../../verifbench/hidden.py)), 513 of 513. It is the only Dafny run of T7 with two such names.

All six `transpose` solutions pass 506 of 506 when built outside the hang. **Corrected, no escaped bug in any arm.** The third refusal, `gcd`, `quod-mcp` #2, has nothing to do with the hang: `--require-contracts` refuses it, with the witness `a = 1, b = -1` and the results 1 and 0, and without a build it has no test result.

**3. The pool of wrong results was weaker than the self-check.** It contains no result of 4 of the 11 known wrong solutions, on its 14 inputs per task: "a separator joins the fold before it", "ties by engine index", "a copy", "strict comparisons". So a post hoc measure, not in the protocol, ran the same contracts on 3 inputs where each wrong solution is wrong ([adequacy-extended.jsonl](adequacy-extended.jsonl)): **still no contract unsound**; 4 Dafny contracts per arm stay undecided, all but two on `next_permutation`.

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

A finite test finds wrong results, it does not exclude them. Six small tasks and one model, whose family also supplies the judge, which answered "adequate" 11 times of 11 and may simply miss faults. The suite has now been read: it is spent. The author read 5 contracts per arm ([contracts-to-read.md](contracts-to-read.md)) and reported no disagreement; there was no "unsure" verdict to read.
