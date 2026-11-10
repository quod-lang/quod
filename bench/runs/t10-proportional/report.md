# T10: the billing engine with a discount shared in proportion

**Question.** [T9](../t9-billing/report.md) kept its rules linear on purpose. Does the one rule it avoided, a product of variables, stop an agent?

The same task and scoring, with one rule changed before any run ([billing.py](../../verifbench/billing.py)): the share of a category is `discount * category_net / subtotal`, and its base is `category_net - share`. Haiku and Sonnet, through MCP with `--require-contracts`, on the released Quod 0.3.1, 2026-11-06. Variants `i64` and `int`, 3 runs each: 12 runs, 4.14 USD. No usage limit, no restart. The hidden tests saw all of 9 wrong rules tried on this one.

> **Reserve on times (review of 0.4.0).** The "Time" column is the agent's, with runs three at a time, under wall-time limits that depended on the load (0.4.0 counts solver operations instead). Read it as an order of magnitude.

## Result

**12 of 12 verified. 12 of 12 pass all 436 orders. 6 of 6 pass all 235 in C# on .NET Framework 4.7.2. 12 of 12 give the client its 4 properties.** No contract left undecided at the end.

| Model, variant | Lines | Lemmas | Time, s | Checks | Rejected | Failed proofs | "Fits in" among them | Cost, USD |
|---|---|---|---|---|---|---|---|---|
| Haiku, `i64` | 427, 477, 397 | 13, 16, 3 | 320, 346, 354 | 10 | 7 | 16 | 10 | 0.55 |
| Haiku, `int` | 430, 371, 295 | 13, 7, 5 | 286, 296, 186 | 10 | 5 | 3 | 0 | 0.42 |
| Sonnet, `i64` | 255, 404, 271 | 6, 8, 8 | 161, 429, 143 | 17 | 12 | 37 | 4 | 1.85 |
| Sonnet, `int` | 242, 378, 256 | 5, 9, 7 | 125, 230, 127 | 16 | 11 | 3 | 0 | 1.33 |

**The product did not stop anyone, and cost nothing that can be seen:** 4.14 USD and 3003 s of agents, against 4.03 USD and 3185 s for T9.

**`i64` costs failed proofs again:** 53 against 6. As in T9, 3 runs per cell: a direction, now seen twice.

## What this does not show

- **One product is not the hard case.** What it needs is a single bound, `0 <= d * n / s <= n`, which a short lemma gives. Nothing here chains products, or asks for a property of a sum of them. **The ceiling is still not reached.**
- The same limits as T9: one author for the compiler, the rules, the oracle and the tests; about 25 rules, 300 lines, no state over time.

## What the agents ran into

The same as in T9, in runs of 12: a helper whose contract only bounds its result (`underspecified` in 6, `returns-argument` in 5), a proof given up on its time limit (7), a statement body used in a contract, or a contract that mentions its own function (3).

The time budget of the whole check was used up in one run, with 21 such messages over its checks.

## Files

`results.jsonl`, `work/*/*.quod`. The transcripts stay on the machine that ran them. No transcript mentions the oracle or a reference. All reads and commands were listed: they stayed in the agent's own directory and its saved tool results, and the commands that looked further were refused.
