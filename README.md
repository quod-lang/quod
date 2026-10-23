# Quod

*English · [Français](README.fr.md)*

*Quod erat demonstrandum*: a programming language designed to be **written by AI agents** and
**checked by machines**. The program comes with its proof.

> **Status: Quod 0.1, young but real.** The compiler checks types, proves contracts with Z3,
> checks that every contract determines its result, and compiles to Python. An AI agent wrote
> the six VerifBench tasks in Quod from the language reference alone, and all six pass the hidden
> tests. No release yet: build it from source (below).

## Thesis

The bottleneck is no longer writing code, it is **trusting** it. Everything that is expensive
for a human (exhaustive contracts, loop invariants, declared effects) is nearly free for an
agent. So Quod requires what humans refuse to write, and in exchange you get code that is
verified rather than merely plausible.

Quod is independent of any LLM: the judge is a solver (SMT), the compiler never calls a model,
and a human can write Quod too, just more tediously.

## Quod 0.1 in one program

```rust
fn binary_search(xs: seq<int>, target: int) -> int
  requires forall i in 0..len(xs): forall j in i..len(xs): xs[i] <= xs[j]   // sorted
  ensures -1 <= result < len(xs)
  ensures result >= 0 ==> xs[result] == target
  ensures result == -1 ==> forall i in 0..len(xs): xs[i] != target
  loose (r1, r2) => (r1 == -1) == (r2 == -1)   // any index of a duplicate will do
{
  let mut lo = 0;
  let mut hi = len(xs);
  while lo < hi
    invariant 0 <= lo <= hi <= len(xs)
    invariant forall i in 0..lo: xs[i] < target
    invariant forall i in hi..len(xs): xs[i] > target
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2;
    if xs[mid] < target { lo = mid + 1; }
    else if xs[mid] > target { hi = mid; }
    else { return mid; }
  }
  return -1;
}
```

```
$ quod check binary_search.quod
verified: 29 proof obligation(s) proved; 1 of 1 contract(s) determine their result; contracts: 1 by properties
```

Every index, every invariant, termination and the postconditions are proved. And the contract
is **complete**: two different results cannot both satisfy it, except where `loose` declares the
freedom (duplicates). A contract that says too little does not compile, and the compiler shows why:

```rust
fn clamp(x: int, lo: int, hi: int) -> int
  requires lo <= hi
  ensures lo <= result <= hi
{
  if x < lo { lo } else if x > hi { hi } else { x }
}
```

```
$ quod check clamp_weak.quod
clamp_weak.quod(4,1): error: in clamp: the contract accepts two different results for the same input: add ensures clauses until only the intended result is allowed, or declare the freedom with 'loose'
    witness: x = 0, lo = -1, hi = 0, result_a = 0, result_b = -1
rejected: 1 proof obligation(s) proved; 0 of 1 contract(s) determine their result, 1 underspecified; contracts: 1 by properties
```

For `x = 0` in `[-1, 0]`, both `0` (the right answer) and `-1` satisfy the contract: it lacks
"`result == x` when `x` is already in range".

`quod build file.quod --target python` then generates a Python module: proved contracts become
documentation, not run-time checks.

## What is here

| Folder | Content |
|---|---|
| [src/Quod/](src/Quod/) | The compiler, in **F#**, shipped as a **Native AOT** binary (no .NET needed to run it): parser, type checker, verifier (Z3 through SMT-LIB), completeness check, Python backend |
| [tests/](tests/) | The compiler's tests (xUnit), among them a differential test of the generated Python against the evaluator |
| [spec/](spec/) | The language: [Quod 0.1](spec/quod-0.1.md) (what exists), [kernel draft](spec/kernel.md) (where it is going) |
| [examples/](examples/) | Programs that verify, and [programs that must be rejected](examples/bugs/) |
| [bench/](bench/) | **VerifBench**: Phase 0 (Python vs Dafny, written by agents), and [the six tasks in Quod](bench/quod/), by hand and by an agent |
| [tools/dafny-complete/](tools/dafny-complete/) | The first building block, for Dafny: a spec-completeness checker that finds concrete witnesses of underspecified contracts |

## Build and try

You need the [.NET 10 SDK](https://dotnet.microsoft.com/download) and the native toolchain that
Native AOT uses (on Windows, the C++ tools of Visual Studio) to build, and
[Z3](https://github.com/Z3Prover/z3/releases) to verify (on the `PATH`, next to `quod`, or in
`QUOD_Z3`).

```bash
dotnet publish src/Quod -c Release -r win-x64 -o artifacts/aot
```

Use `linux-x64` or `osx-arm64` for another system. Then:

```bash
artifacts/aot/quod check examples/binary_search.quod
```

## What we learned so far

*Phase 0 in full: [Green proofs, empty promises: when AI agents write their own specifications](https://dev.to/malek_aitouaret_f026758c/green-proofs-empty-promises-when-ai-agents-write-their-own-specifications-59lf) (dev.to).*

- **Phase 0, Dafny.** Asked to write *verified* Dafny, a smaller model produced contracts that
  verify but barely say anything: 5 of 8 only constrained a length, a format or a shape. One of
  those methods was wrong, and the proof did not notice. Hence Quod's
  [pillar 5](spec/kernel.md#5-complete-specifications): every contract must determine its result.
- **Quod 0.1, by an agent.** Given only the [language reference](spec/quod-0.1.md#the-language),
  an agent wrote the six VerifBench tasks without strings; all six verify and pass the hidden
  tests ([run quod1](bench/quod/README.md#an-agent-writes-them)). No weak contract got through.
- **But a complete contract can still say how rather than what.** Four of the six defined the
  result by a second implementation, or restated the body. `quod check` now reports the
  [style of every contract](spec/quod-0.1.md#contract-style) (properties, model, restated,
  missing), with a warning for the last two.
- **A smaller agent finds the holes.** A Haiku run found three ways around the completeness
  check (a contract no solver model could refute, a `loose` that accepts everything, no ensures
  at all), each now caught.

## Roadmap

0. **Measure** (done): does verification reduce escaped bugs, and at what cost?
   First tool shipped: [dafny-complete](tools/dafny-complete/).
1. **Quod 0.1** (nearly done): pure functions on integers, booleans, sequences and tuples, with
   contracts, the completeness check and a Python backend. Left: JSON diagnostics polish and
   Native AOT releases for Windows, Linux and macOS.
2. **Quod 0.2**: strings, algebraic types, modules, generics, a `lemma` construct, an MCP server
   for agents.
3. **Quod 0.3**: capabilities (no ambient authority: a function touches the console, files or
   the network only through a capability it receives), sealed contracts, maps and sets.
4. **Quod 0.4**: a C backend, towards native code and WASM.
5. **Quod 2.0 will be written in Quod.**

Development happens in the open. If you write Dafny, or let agents write code you need to trust,
issues and discussions are very welcome.

## License

Quod is and will stay **free**.

- Compiler, tools and benchmark: **[Apache 2.0](LICENSE)**, permissive, with a patent clause
  that protects users.
- Language specification ([spec/](spec/)): **[CC BY 4.0](spec/LICENSE)**, so anyone can write
  their own implementation, with attribution.

## Related work

- **Dafny, F\*, Lean, Verus**: languages with built-in verification; Dafny is the reference
  point of Phase 0, and Quod's encoding of sequences follows its axioms.
- **Specification quality for LLM-written code**: Lahiri's symbolic testing of Dafny
  specifications ([FMCAD 2024](https://arxiv.org/abs/2406.09757)) is the direct ancestor of the
  witness search; see also MutDafny, nl2postcond, Clover and the intent-formalization agenda,
  summarized in [docs/related-work.md](docs/related-work.md).
- **Unison**: content-addressed code.
- **[Warrant](https://github.com/mv2a/warrant)**: a language-agnostic evidence protocol for
  agent-written code. Very close in intent; Quod sits one layer below (the language itself) and
  could be a producer of proofs for it.
