---
title: "Green proofs, empty promises: when AI agents write their own specifications"
published: true
canonical_url: https://dev.to/malek_aitouaret_f026758c/green-proofs-empty-promises-when-ai-agents-write-their-own-specifications-59lf
tags: dafny, formalverification, ai, llm
---

I asked AI coding agents to write **formally verified** code. Every solution passed the
verifier. Then I checked what the proofs actually promised.

For the smaller model, **5 of 8 specifications barely said anything**. One of the
methods was wrong, and its proof was green.

This post is about that gap, a cheap way to detect it, and a small open-source tool that does it
for any Dafny file.

## The experiment

I'm designing a programming language meant to be written by agents and checked by machines
(more on that at the end). Before designing anything, I wanted data: **when an agent has to prove
its code, do fewer bugs slip through?**

The setup ([VerifBench](https://github.com/quod-lang/quod/tree/main/bench)):

- 8 short algorithmic tasks chosen because LLMs classically stumble on them: Gregorian
  day counting (leap centuries), strict UTF-8 validation (overlongs, surrogates), glob matching
  with escapes, an LRU cache, a lexicographically smallest topological sort, text justification,
  big-number addition (borrows, `-0`), Unix path normalization.
- Same natural-language spec, two arms: plain **Python** (the agent may run its own tests), or
  **Dafny**, where the agent must write `requires` / `ensures` / invariants and get
  `dafny verify` to pass. Cheats like `assume` or `{:verify false}` are detected.
- Claude Code as the agent, two models: `claude-opus-5-5` and `claude-haiku-4-5`.
- About 500 **hidden tests** per task, compared with an oracle. The Dafny code is compiled to
  Python and goes through exactly the same tests.

The key metric is the **escaped bug**: a solution the agent would ship (and, in Dafny, that
verifies) which still fails a hidden test.

## The results look reassuring...

| Model / arm | Escaped bugs | Cost per task* | Time per task |
|---|---|---|---|
| Opus / Python | 0 / 8 | $0.14 | 17 s |
| Opus / Dafny | 0 / 8 | $0.22 | 46 s |
| Haiku / Python | 1 / 8 | $0.15 | 106 s |
| Haiku / Dafny | 1 / 8 | $0.45 | 255 s |

<small>* API-equivalent estimate reported by the agent. One trial per cell: signals, not statistics.</small>

Opus solved everything, with or without proofs. Haiku let one bug through in each arm. Proof
looks like it costs 1.5–3× more and buys... nothing here?

## ...until you read the Haiku Dafny bug

The escaped Dafny bug was in the LRU cache. The method **verified**. Here is its signature
(preconditions abridged) and its entire postcondition:

```dafny
method lru_cache(capacity: int, ops: seq<(int, int, int)>) returns (out: seq<int>)
  requires capacity >= 1
  ensures |out| == CountGets(ops, |ops|)
```

The output has the right *length*. Nothing says which values a `get` returns. The code evicted
an entry every time a new key was inserted, whether the cache was full or not, and Dafny was
perfectly happy, because nothing in the contract forbade it.

A verifier only guarantees what you ask it to. And when the agent writes **both** the code and
the specification, it can, without any malice, ask for exactly as much as it manages to prove.

So I went back and checked all 24 Dafny contracts.

## A simple question to ask a specification

For a method with precondition `R` and postcondition `E`, ask:

> Can two **different** results both satisfy `E`, for the same valid input?

If the contract is complete, the answer is no:

```
∀ x, a, b :  R(x) ∧ E(x, a) ∧ E(x, b)  ⇒  a == b
```

This is a question about the **contract only**, not the code. And Dafny can answer it: generate
a lemma with exactly that statement and ask Dafny to prove it, with no hints.

```dafny
ghost predicate Post(capacity: int, ops: seq<(int,int,int)>, out: seq<int>)
  requires capacity >= 1
{ |out| == CountGets(ops, |ops|) }

lemma Uniq(capacity: int, ops: seq<(int,int,int)>, a: seq<int>, b: seq<int>)
  requires capacity >= 1 && Post(capacity, ops, a) && Post(capacity, ops, b)
  ensures a == b
{}
```

When the proof goes through, the contract determines the result. When it fails, that may mean
the contract is incomplete... or just that the uniqueness proof is hard (it often needs
induction). To tell the two apart, you need a **witness**.

## Finding witnesses

The trick: take small concrete inputs, **run the method** to get its actual answer `a`, build
neighbouring answers `b` (a changed digit, a dropped element, an emptied list...), and ask Dafny
to *prove* that the contract accepts both `a` and `b` on those concrete values.

If both proofs go through, you have a certain witness: no sampling, no guessing. Results on the
24 agent-written contracts:

| Verdict | Count |
|---|---|
| Uniqueness proved | 15 |
| **Underspecified, with a witness** | 6 |
| Inconclusive | 3 |

The six witnesses:

| Method | Input | Two results the contract accepts |
|---|---|---|
| `add_big` (Haiku) | `"0" + "0"` | `"0"` and `"1"` |
| `topo_sort` (Haiku) | 1 node, no edge | `[0]` and `[]` |
| `normalize_path` (Haiku) | `""` | `"."` and `".x"` |
| `justify` (Haiku) | `["a"]`, width 2 | `["a "]` and `[]` |
| `lru_cache` (Haiku) | two `get`s on an empty cache | `[-1, -1]` and `[0, -1]` |
| `binary_search` | `[1, 1]`, target 1 | `1` and `0` |

Read them as sentences and they speak for themselves: according to its proved contract, the
addition is allowed to say 0 + 0 = 1. The topological sort may return nothing for a graph with
no edge. The path normalizer may return any non-empty string.

The last one, `binary_search`, is **legitimately** free: with duplicates, any index of the target
is a correct answer. A witness doesn't mean "bug"; it means "the contract allows a choice", and
someone should decide whether that choice is intended.

The striking part: **four of Haiku's five near-empty contracts sat on correct code**. The tests
passed, the proofs were green, and the proofs guaranteed almost nothing. Without this check,
"verified" on those methods was pure decoration.

And the three inconclusive ones? I read them: their contracts *are* complete (merging intervals
into a canonical union, run-length encoding, canonical decimal strings), but proving uniqueness
needs induction that the solver won't find alone. No witness was found for any of them, so the
tool never reported them as underspecified. Clean separation, on this small sample.

Opus, for the record, wrote contracts that were proved unique in 7 of 8 hard tasks, including a
full lexicographic-minimality specification for the topological sort.

## The tool: dafny-complete

I turned this into a standalone checker that works on any `.dfy` file:

```bash
pipx install "git+https://github.com/quod-lang/quod#subdirectory=tools/dafny-complete"
dafny-complete my_file.dfy
```

```
  [OK]    Abs      line 11    the contract determines a unique result
  [UNDER] WeakAbs  line 19    the contract accepts two different results
                    input  : x=0
                    y = 0   (what the method returns)
                    y = 1   (also satisfies every ensures)
```

It runs four Dafny passes over the whole file (uniqueness lemmas, valid small inputs proved
against the preconditions, actual execution of the methods, witness lemmas) and never modifies
your file. Exit code 1 when something is underspecified, so it can sit in CI, or in an agent's
loop: `--json` gives the witness in machine-readable form, which is exactly the feedback an agent
needs to strengthen its contract.

Without access to the benchmark's oracle, it reproduces all 24 verdicts. Run on the whole
`add_big` file rather than just the main method, it also flags the three helpers Haiku wrote
(`AddAbsolute` accepts `"10" + "10" = "201"`): the weakness was not one slip, but the way the
whole file was specified.

## Limitations, honestly

- **Small sample.** 8 tasks per suite, one trial per cell, one agent family. The pattern is
  vivid, but it is a signal, not a measurement.
- **Complete is not correct.** A contract can pin down a single, wrong result. The check
  removes specifications that are too *weak*, not ones that are *mistaken*.
- **The second-program trap.** A postcondition like `out == Model(ops)`, where `Model`
  reimplements the problem, is always "complete", and can carry the same bug as the code.
- **Witness search is heuristic.** Neighbours come from simple rules; a contract can be
  incomplete in a subtler way and come out "inconclusive". Supported types for witnesses: `int`,
  `nat`, `bool`, `char`, `string`, `seq<T>`, tuples. Instance methods and heap-touching methods
  are skipped for now.

## Why I care: Quod

This started as Phase 0 of [Quod](https://github.com/quod-lang/quod), a language designed to be
written by AI agents and checked by machines. The bet: everything that is expensive for humans
(exhaustive contracts, invariants, declared effects) is nearly free for an agent, so a language
can demand it.

This experiment changed the design. In Quod, the completeness check is built into the compiler:
an underspecified function **does not compile**, and the error comes with the witness. When
several answers are legitimately acceptable, you say so explicitly, with a relation between two
acceptable results:

```rust
fn binary_search(xs: &[i64], target: i64) -> Option<usize>
  requires sorted(xs)
  ensures ...
  loose (r1, r2) => r1.is_some() == r2.is_some()   // which index may vary; found/not found may not
```

Freedom becomes a visible, checked decision instead of an oversight.

Everything is open: the benchmark with every agent transcript, the language draft, and the tool
(Apache 2.0). If you write Dafny, I'd love to know what `dafny-complete` finds, or misses, on
your code. Issues and discussions are open at
[github.com/quod-lang/quod](https://github.com/quod-lang/quod).
