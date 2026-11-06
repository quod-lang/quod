# T8: an agent on the features of 0.3

**Question.** With the reference alone, can an agent write verified programs with the features of 0.3, and what does `i32` cost it, against `int`?

Haiku (`claude-haiku-5-5`), through the MCP server with `--require-contracts`, on the released Quod 0.3.0, 2026-11-06. 12 task variants of [features.py](../../verifbench/features.py), 3 runs each, 3 at a time: 36 runs, no usage limit, 0.29 USD. Every variant was first done by hand, to see that it can be done and that its hidden tests are right. No change to the compiler during the runs.

## Result

**36 of 36 verified, and 36 of 36 pass their hidden tests.** C#: 33 of 36 compile on .NET Framework 4.7.2, C# 7.3. All 3 failures are `module_total`.

| Task | Feature | Checks, per run | Rejected checks, of them | Failed proofs | C# compiles |
|---|---|---|---|---|---|
| `clamp_i32` | `i32` overflow | 1, 1, 1 | 0 | 0 | 3/3 |
| `clamp_int` | none | 1, 3, 3 | 0 | 0 | 3/3 |
| `discount_i32` | enum, match, `i32` | 3, 3, 3 | 6 | 0 | 3/3 |
| `discount_int` | enum, match | 2, 2, 3 | 1 | 0 | 3/3 |
| `total_i32` | `i32`, `i64`, loop | 1, 1, 1 | 0 | 0 | 3/3 |
| `total_int` | loop | 3, 2, 3 | 4 | 1 | 3/3 |
| `invoice_total` | struct, `i32`, loop | 1, 3, 1 | 2 | 1 | 3/3 |
| `first_index` | `Option`, loop | 1, 2, 1 | 1 | 1 | 3/3 |
| `generic_last` | generics | 1, 1, 1 | 0 | 0 | 3/3 |
| `module_total` | modules, struct | 1, 2, 1 | 1 | 0 | **0/3** |
| `parse_kv` | strings, library, `Option` | 5, 2, 2 | 6 | 0 | 3/3 |
| `step` | nested match, `Result` | 2, 2, 1 | 2 | 0 | 3/3 |

**On `i32`: no cost could be seen, on tasks this small.** Over the three pairs, `i32` took 15 checks and `int` 22; 6 rejected against 5. No failed proof in these pairs says a result does not fit. The one difference against `i32`, `discount_i32`, is a type error, not a proof (below). `total_int` costing more than `total_i32` is 3 runs against 3, and should not be read as a gain.

## What this does not show

- **The tasks are easy: there is a ceiling.** Most runs finish in under 30 s. This shows that the features can be written from the reference, not that they hold on a real program, nor how a harder task behaves.
- **The contracts were not measured.** Hidden tests judge the code. The contracts passed the check for completeness, and the ones read by hand say what the task asks (6 programs, by the author of the tasks), but no adequacy measure ran.
- **One model, 3 runs per variant, tasks written by the author of the compiler**, with the frictions met while writing the reference solutions still in mind.

## What the agents ran into

Counted in runs, from their transcripts.

1. **A generated program that does not compile: `Money` in module `money`, 3 of 3.** `CS0542`: a class cannot have a member of its own name. The notes list it among rare names; the task asked for this name, and it is the natural one.
2. **`Ok`, `Err`, `Some`, `None` for `option.Ok`...: 5 of the 6 runs of `step` and `parse_kv`.** `unknown function 'Err'`, with no hint of the module. Every one of them found it.
3. **A literal in a `match` or an `if` is not adopted by an `i32`: all 3 `discount_i32` runs.** `the body has type int, but i32 is expected`. They went through `to_i32(...)`, with a proof obligation that nothing needed.
4. **A function with a statement body cannot be used in a contract: 4 runs**, of `parse_kv`, `invoice_total` and `discount_i32`, on their own helpers. They rewrite the helper as an expression: the message is clear, the cost is a turn. The same goes for `strings.find` of the library, met while writing the reference of `parse_kv`.
5. **`i32 * i32` stays `i32` when returned as `int`: 1 of 3 `invoice_total`.** Refuted with a counterexample, and fixed at once.

## Files

`results.jsonl`, and `work/*/solution.quod` (with `money.quod`). The transcripts stay on the machine that ran them: they hold its configuration.
