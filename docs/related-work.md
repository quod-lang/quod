# Related work: checking the strength of (LLM-written) specifications

*Written 2026-10-21 after publishing dafny-complete. Lahiri 2024 was read in its arXiv HTML
version; the other entries are summarized from their abstracts and from search results and should
be read in full before being cited in detail.*

## Closest prior work

**Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages",
FMCAD 2024** ([arXiv 2406.09757](https://arxiv.org/abs/2406.09757)).
Symbolically tests Dafny specifications against input/output test cases:

- *correctness (soundness)*: `{true} x := i; y := o {φ(x, y)}` holds for every test `(i, o)`;
- *completeness*: the fraction of **mutated outputs** `o'` for which that Hoare triple does not
  verify (a kill rate, inspired by mutation testing);
- implemented as a ~400-line Python script generating Dafny programs; evaluated against human
  `strong_spec` / `weak_spec` labels on ~150 MBPP-based Dafny specifications (mostly GPT-4
  generated). Its example of a weak spec (`count` only constrained to be non-negative) is exactly
  the kind of contract we found.
- Appendix B discusses a per-test uniqueness check, `{x == i ∧ φ} skip {y == o}`, and sets it aside
  because it only gives a Boolean verdict and only rewards specifications that constrain the output
  to a unique value.

**This is the same core idea as dafny-complete's witness step** (mutate an output on a concrete
input, ask Dafny), published two years earlier. We should have cited it from the start.

## Other related work

- **Endres et al., nl2postcond** (FSE 2024, [arXiv 2310.01831](https://arxiv.org/abs/2310.01831)):
  LLM-generated postconditions for mainstream languages; completeness measured by how many *code
  mutants* of a reference implementation a postcondition rejects. Needs reference code and tests.
  Follow-ups: [Beyond Postconditions](https://arxiv.org/abs/2510.12702) (LLMs biased towards
  simple, incomplete postconditions), [PostCondBench](https://arxiv.org/abs/2605.03356).
- **Sun et al., Clover** (Dafny workshop @ POPL 2024, [arXiv 2310.17807](https://arxiv.org/abs/2310.17807)):
  checks *consistency* between code, docstring and Dafny annotations; the verifier check is exact,
  the docstring/annotation checks rely on an LLM.
- **Lahiri, "Intent Formalization: A Grand Challenge for Reliable Coding in the Age of AI Agents"**
  (2026, [arXiv 2603.17150](https://arxiv.org/abs/2603.17150)): names *validating specifications*
  as the central bottleneck and calls for semi-automated metrics of specification quality, with or
  without code.
- **Vacuous / weakened specifications** are a documented failure mode: the
  [vericoding benchmark](https://arxiv.org/abs/2509.22908) reports models giving trivial solutions
  to weak specs; [SWE-Proof](https://arxiv.org/abs/2609.21190) audits passes for spec integrity
  because weakening the spec until the proof goes through is an obvious temptation for an agent;
  [Verus-SpecGym](https://arxiv.org/abs/2605.26457) finds that an LLM judge misses many incorrect
  specifications that a failing test exposes; [SpecRL](https://arxiv.org/abs/2604.05820) uses
  test-based completeness as a training reward.

## What dafny-complete adds (modestly)

| | Lahiri 2024 | nl2postcond | dafny-complete |
|---|---|---|---|
| Needs tests (input/output pairs) | yes | yes | **no**: runs the method itself |
| Needs reference code / code mutants | no | yes | no |
| Universal check over all inputs | no (per test) | no | **yes**: a uniqueness lemma, proved symbolically |
| Meaning of a "mutant" verdict | verification *failed* ⇒ counted as killed (an unknown is read as a kill) | test-based | witness only when acceptance is **proved** ⇒ an UNDER verdict is certain |
| Output | a score per specification | a score | per-method verdict with a concrete witness, CLI + JSON for agents |

The empirical part (agent-written contracts in a Python-vs-Dafny benchmark, with hidden tests) is
small but, as far as this review goes, a fresh data point: most of a smaller model's contracts
were near-empty, mostly on correct code.

For Quod, the design consequence stands and goes beyond a metric: completeness becomes a **compile
rule** with a declared escape hatch (`loose`), instead of a score computed after the fact.
