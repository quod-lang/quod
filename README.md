# Quod

*English · [Français](README.fr.md)*

*Quod erat demonstrandum*: a programming language designed to be **written by AI agents** and
**checked by machines**. The program comes with its proof.

## Thesis

The bottleneck is no longer writing code, it is **trusting** it. Everything that is expensive
for a human (exhaustive contracts, loop invariants, declared effects) is nearly free for an
agent. So Quod requires what humans refuse to write, and in exchange you get code that is
verified rather than merely plausible.

Quod is independent of any LLM: the judge is a solver (SMT), the compiler never calls a model,
and a human can write Quod too, just more tediously.

## What is here

| Folder | Content |
|---|---|
| [tools/dafny-complete/](tools/dafny-complete/) | **First building block, usable today**: a spec-completeness checker for Dafny that finds concrete witnesses of underspecified contracts |
| [bench/](bench/) | **Phase 0, VerifBench**: measuring what verification brings when agents write code (Python vs Dafny, Opus vs Haiku) |
| [spec/](spec/) | The language design: [kernel draft](spec/kernel.md) |
| `src/` | *(to come)* compiler: parser, verifier (Z3), code generation, in C#/.NET |

## What we learned so far

*Full story: [Green proofs, empty promises: when AI agents write their own specifications](https://dev.to/malek_aitouaret_f026758c/green-proofs-empty-promises-when-ai-agents-write-their-own-specifications-59lf) (dev.to).*

- Asked to write *verified* Dafny, a smaller model produced contracts that verify but barely
  say anything: 5 of 8 only constrained a length, a format or a shape. One of those methods was
  wrong, and the proof did not notice.
- A verifier only guarantees what it is asked. Hence Quod's
  [pillar 5](spec/kernel.md#5-complete-specifications): the compiler proves that each contract
  pins down a **unique** result, or shows a concrete witness of two results it accepts.
- Measured on 24 agent-written Dafny solutions, that check finds all 6 underspecified contracts,
  with no false verdict ([details](bench/README.md#spec-completeness-pillar-5)).

## Design in one page

1. **Mandatory contracts**: `requires` / `ensures` on every function, invariants on every loop.
2. **Effects through capabilities**: no ambient authority. A function can only touch the console,
   files, clock or network if it *receives* a capability for it, so its signature says everything
   it can do.
3. **Refinement types**: `type Percent = i32 where 0 <= _ && _ <= 100`.
4. **Diagnostics for agents**: structured JSON with concrete counterexamples.
5. **Complete specifications**: an underspecified contract does not compile, unless the freedom
   is declared with a `loose` clause.

```rust
fn greet(out: Console, name: str)
  requires len(name) > 0
  ensures out.written == old(out.written) + [greeting(name) + "\n"]
{
  out.write_line(greeting(name))
}

fn main(sys: System) {
  greet(sys.console, "world")
}
```

## Roadmap

0. **Measure** (done, see [bench/](bench/)): does verification reduce escaped bugs, and at what
   cost? First tool shipped: [dafny-complete](tools/dafny-complete/).
1. **Minimal kernel**: front end in C#, verification conditions to Z3, C# code generation;
   pure functions with contracts and the completeness check.
2. **Agent interface**: JSON diagnostics with counterexamples and witnesses, an MCP server.
3. **Capabilities** and their runtime.
4. **Performance**: LLVM/MLIR and WASM back ends.

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
  point of Phase 0.
- **Specification quality for LLM-written code**: Lahiri's symbolic testing of Dafny
  specifications ([FMCAD 2024](https://arxiv.org/abs/2406.09757)) is the direct ancestor of
  `dafny-complete`'s witness search; see also nl2postcond, Clover and the intent-formalization
  agenda, summarized in [docs/related-work.md](docs/related-work.md).
- **Unison**: content-addressed code.
- **[Warrant](https://github.com/mv2a/warrant)**: a language-agnostic evidence protocol for
  agent-written code. Very close in intent; Quod sits one layer below (the language itself) and
  could be a producer of proofs for it.
