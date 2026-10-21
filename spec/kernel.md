# Quod kernel, draft v0

*English · [Français](kernel.fr.md)*

> Status: design notes, not yet a normative specification. The choices below are hypotheses that
> Phase 0 ([bench/](../bench/)) is meant to confirm or refute.

## Principles

1. **Familiar syntax, new semantics.** A surface close to Rust/OCaml, to reuse what models
   already know; the novelty lies in contracts, effects and verification. The grammar is short
   enough to fit entirely in a prompt.
2. **No property silently ignored.** Every declared property has a status:
   - ✅ **proved** statically (SMT);
   - ⚠️ **checked at run time**: the proof failed or timed out, so a check is inserted *and reported*;
   - ❌ **refuted**, with a concrete counterexample.
3. **The compiler talks to machines.** Its primary output is structured (JSON), not prose.
4. **No undefined behaviour, determinism by default.**
5. **No ambient authority.** Every access to the outside world goes through a capability received
   as a parameter (see pillar 2).

## The five pillars

### 1. Mandatory contracts

Every public function carries `requires` / `ensures`; every loop, `invariant` and `decreases`.

```rust
fn binary_search(xs: &[i64], target: i64) -> Option<usize>
  requires sorted(xs)
  ensures match result {
    Some(i) => i < len(xs) && xs[i] == target,
    None    => forall j in 0..len(xs): xs[j] != target,
  }
  loose (r1, r2) => r1.is_some() == r2.is_some()   // see pillar 5
{
  let mut lo: usize = 0;
  let mut hi: usize = len(xs);
  while lo < hi
    invariant lo <= hi && hi <= len(xs)
    invariant forall j in 0..lo: xs[j] < target
    invariant forall j in hi..len(xs): xs[j] > target
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2;
    if xs[mid] < target      { lo = mid + 1 }
    else if xs[mid] > target { hi = mid }
    else                     { return Some(mid) }
  }
  None
}
```

### 2. Effects through capabilities

Quod has **no ambient authority**: no console, file system, clock or network reachable
globally. To act on the outside world, a function must **receive a capability** as a parameter.
The signature alone therefore says everything a function *can* do.

```rust
fn load_config(fs: FsRead, path: Path) -> Config
  effects { fail(ParseError) }
```

`load_config` can read files, and nothing else: it cannot write, open the network or read the
time. A reviewer (human or agent) does not need to read the body to know that.

#### Rules

1. **Capabilities are unforgeable.** There is no public constructor: the only source is the
   `sys: System` parameter the runtime passes to `main`. You cannot create one, nor store one in
   a constant or global state (there is no mutable global state).
2. **They are passed explicitly**, like any other value: `greet(sys.console)`. A function only
   has authority over the capabilities reachable from its parameters.
3. **They can be attenuated, never amplified.** You can derive a narrower capability, never the
   reverse:

   ```rust
   let data: Fs     = sys.fs.subdir("data")   // confined to ./data
   let ro:   FsRead = data.read_only()        // read only
   ```

   Subtyping: `Fs <: FsRead`, so an `Fs` can be passed where an `FsRead` is expected.
4. **Determinism is structural.** The clock (`Clock`) and randomness (`Rand`) are capabilities
   too: a function that receives neither is deterministic by construction.
5. **The `effects` clause keeps only intrinsic effects**, those that do not go through a
   capability: `fail(E)` (propagated error), `alloc`, `diverge` (termination not proved). When
   omitted it is `{}`. A function with no capability parameter and no `effects` is **pure**.

#### Kernel capabilities

| Type | Authority | Attenuations |
|---|---|---|
| `System` | root, received by `main` only | its fields below |
| `Console` | write stdout/stderr, read stdin | `.stdout_only()` |
| `Fs` / `FsRead` | file system | `.subdir(p)`, `.read_only()` |
| `Clock` | current time | — |
| `Rand` | randomness | `.seeded(n)` (becomes deterministic) |
| `Net` | network | `.only_host(h)` |
| `Env` | environment variables, arguments | `.only(keys)` |

#### Specifiable effects

Each capability exposes a **ghost model**, visible only in contracts, describing its observable
state. For `Console` it is `written: seq<str>`, everything written so far. Effects thus become
part of what is proved:

```rust
fn greet(out: Console, name: str)
  requires len(name) > 0
  ensures out.written == old(out.written) + [greeting(name) + "\n"]
{
  out.write_line(greeting(name))
}
```

#### Tests without mocking magic

Since authority arrives as a parameter, a test simply passes a recording capability:

```rust
test greet_writes_one_line {
  let c = Console.recorder()
  greet(c, "Ada")
  assert c.written == ["Hello, Ada!\n"]
}
```

#### Diagnostic

Using an authority you did not receive is a compile error, with a proposed fix:

```json
{
  "status": "error",
  "code": "capability_missing",
  "location": { "fn": "greet", "line": 4 },
  "message": "`greet` writes to the console but receives no `Console` capability",
  "fix": { "add_parameter": "out: Console", "update_callers": ["main"] }
}
```

#### Why this choice (rather than a plain `effects { console.write }` clause)

- **Least privilege**: `main` hands each function only what it needs, and attenuation
  (`subdir`, `read_only`) restricts more finely than a list of effects.
- **Audit**: agent-written code cannot "cheat" by reaching a global resource; every path to the
  outside world is visible in signatures and in `main`.
- **Testability**: you substitute capabilities, no mocking framework needed.
- **Price**: longer signatures and capabilities to thread through, exactly the kind of verbosity
  that costs a human a lot and an agent almost nothing.

### 3. Refinement types

```rust
type Percent = i32 where 0 <= _ && _ <= 100
type Index<xs> = usize where _ < len(xs)
```

An access `xs[i]` with `i: Index<xs>` is proved in bounds: no bounds check at run time.

### 4. Diagnostics for agents

```json
{
  "status": "refuted",
  "property": "ensures #2 (None => forall j ...)",
  "location": { "fn": "binary_search", "line": 5 },
  "counterexample": { "xs": [1, 3, 5], "target": 3, "returned": "None" },
  "hint": "invariant #3 not preserved when xs[mid] > target"
}
```

The counterexample is the most valuable thing you can give an agent: a concrete case to fix
rather than a hypothesis to guess.

### 5. Complete specifications

A verifier only guarantees what it is asked to. A specification that is too weak is worse than
no specification: it produces **false confidence**.

**Phase 0 finding** (`bench/runs/hard1`): on `lru_cache`, Haiku wrote wrong Dafny code that was
*fully proved*, because its only guarantee was

```dafny
ensures |out| == CountGets(ops, |ops|)   // the length is right... the content is free
```

#### The check

For each function, besides proving the body, the verifier proves that the contract
**determines the result uniquely**:

```
∀ inputs satisfying requires, ∀ r₁ r₂ :  ensures(r₁) ∧ ensures(r₂)  ⇒  r₁ == r₂
```

The "result" includes the return value **and** the ghost state of capabilities after the call
(`out.written`, ...): an underspecified effect is caught like an underspecified value.

The check looks only at the contract, never at the body: it is a question asked of the
specification itself, "does it allow more than one answer?".

#### Statuses

- ✅ **determined**: uniqueness is proved;
- ❌ **underspecified**, with a **witness**: an input and two distinct results, the contract being
  *proved* on each. The verdict requires that witness: no witness, no ❌;
- ⚠️ **inconclusive**: neither a uniqueness proof nor a witness; reported, never ignored
  (principle 2).

An underspecified function **does not compile**, unless the freedom is declared (below). An
inconclusive one compiles with a warning; the agent can add a uniqueness lemma.

To find a witness when the uniqueness proof fails, the compiler tries small concrete inputs and
results neighbouring the answer the code actually produces. Measured in Phase 0 on 24 Dafny
solutions: the 6 truly underspecified contracts all got a witness, the 3 false alarms (canonical
forms whose uniqueness needs induction) got none. This check is available today for Dafny as
[dafny-complete](../tools/dafny-complete/).

```json
{
  "status": "underspecified",
  "fn": "lru_cache",
  "witness": {
    "input": { "capacity": 1, "ops": [[0, 0, 0], [0, 0, 1]] },
    "result_a": [-1, -1],
    "result_b": [0, -1]
  },
  "hint": "ensures constrains only |out|; both results satisfy it"
}
```

Facing this witness, the agent sees at once what is missing: nothing says *which* value a `get`
must return.

#### Declared freedom: `loose`

Some functions legitimately have several correct answers. That is **declared**, by stating
precisely what may vary, as a relation between two acceptable results:

```rust
fn binary_search(xs: &[i64], target: i64) -> Option<usize>
  requires sorted(xs)
  ensures match result {
    Some(i) => i < len(xs) && xs[i] == target,
    None    => forall j in 0..len(xs): xs[j] != target,
  }
  // With duplicates, any index of `target` will do;
  // but found / not found is determined.
  loose (r1, r2) => r1.is_some() == r2.is_some()
```

The check then proves `ensures(r₁) ∧ ensures(r₂) ⇒ loose(r₁, r₂)` instead of `r₁ == r₂`. Without
a `loose` clause the relation defaults to equality. Freedom thus becomes **a visible, checked
decision** rather than an oversight.

#### What the check does not guarantee

- **Complete does not mean right.** A specification can determine a unique result... that is
  wrong. The check eliminates specifications that are too *weak*, not ones that are *mistaken*:
  matching the intent still has to be validated (review, examples, property tests).
- **The second-program trap.** A specification like `ensures out == Model(ops)`, where `Model`
  is a functional reimplementation, always passes the check, and can carry the same bug as the
  code. The diagnostic flags that style (*spec by model*) to encourage declarative properties
  (quantifiers, invariants) where possible. Observed in Phase 0 on `bounded_queue`.
- **Cost**: one more SMT query per function, often harder than proving the body (two symbolic
  results).

## Open questions

- **Complete specifications (pillar 5)**: measured on the 24 Dafny solutions of Phase 0 (see
  [dafny-complete](../tools/dafny-complete/)): uniqueness is proved unaided for 15, and the 3
  failures on complete specifications are canonical forms. Still to measure on real code: the
  share of functions that need `loose`, and scaling to rich structures (maps, sets, heap).
- **Decidability and proof time**: which logical fragment to guarantee to avoid SMT timeouts?
- **Capabilities and concurrency**: how to share a capability between parallel tasks (copy,
  borrowing, linearity) without losing the precision of the ghost model?
- **Content-addressed code** (Unison style): in the kernel, or later?
- **AST edits** rather than text edits: which interface to expose to agents?
- **Relation to Warrant**: Quod as a proof producer for that protocol?
