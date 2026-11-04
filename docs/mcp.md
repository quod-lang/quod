# Quod as a tool for AI agents (MCP)

*English · [Français](mcp.fr.md)*

`quod mcp` is a [Model Context Protocol](https://modelcontextprotocol.io) server: an agent checks,
builds and runs Quod programs through it, without a shell, and reads the language reference from
it. It is part of the `quod` binary of the [release](https://github.com/quod-lang/quod/releases/latest),
with z3 next to it: nothing else to install.

## Tools

| Tool | What it does |
|---|---|
| `quod_check` | Types, proofs (z3) and completeness of a program given as `source` (its text) or `path`. Returns the diagnostics, with counterexamples, and a summary line that starts with `verified` or `rejected`. Options: `timeout`, `budget`. |
| `quod_build` | Checks, then returns the generated Python module as text (no file written). Only a verified program is built, unless `runtime_checks` is true. |
| `quod_run` | Runs one function on given arguments (JSON numbers, booleans, arrays), checking every assertion, invariant, bound and contract on the way. Returns the result, or the obligation that fails, with its text (and the value returned, for a postcondition). |
| `quod_reference` | The language reference, or one `section` of it (`Hints and lemmas`, `Contract style`...). Also a resource: `quod://reference`. |

Each tool returns a text for the agent and the same facts as JSON (`structuredContent`).

## Install

Replace `/path/to/quod` with where you unpacked the release (`quod.exe` on Windows).

**Claude Code**

```bash
claude mcp add quod -- /path/to/quod mcp
```

**Clients that read `mcpServers`** (Claude Desktop, Cursor in `.cursor/mcp.json`, Gemini CLI,
a project `.mcp.json`):

```json
{
  "mcpServers": {
    "quod": { "command": "/path/to/quod", "args": ["mcp"] }
  }
}
```

**VS Code** (`.vscode/mcp.json`):

```json
{
  "servers": {
    "quod": { "type": "stdio", "command": "/path/to/quod", "args": ["mcp"] }
  }
}
```

**Codex CLI** (`~/.codex/config.toml`):

```toml
[mcp_servers.quod]
command = "/path/to/quod"
args = ["mcp"]
```

The server speaks MCP over stdio (one JSON-RPC message per line). It needs no environment
variable: z3 is found next to `quod` (or in `QUOD_Z3`, then on the `PATH`). `path` arguments are
relative to the server's working directory: the one the client starts it in, usually the
project.

A check through the server has a **time budget of 60 s** by default, since an agent waits for
the tool call (the command line has 300 s): obligations left when it is used up are reported as
`not-attempted`, not as failures. An agent can ask for more with the `budget` argument, and
`quod mcp --budget 120` changes the default (`--timeout` too, 10 s per obligation).

`quod mcp --require-contracts` makes a function without a contract, a `loose` that accepts every result, a lemma
written as a function, or a `requires` that fixes a parameter, an error, so an agent cannot stop at a file that verifies because it states nothing. It is set on the server: the agent has no
argument to turn it off.

Tool calls run one at a time, while the server keeps reading: `ping`, `tools/list` and the
resources are answered at once, `notifications/cancelled` stops the call it names (z3 is killed,
and no response is sent), and a call that gives a `progressToken` gets progress notifications:
when each function and each completeness check starts and ends, and when a try of the solver has
run for a second (`f: invariant #2, solver, up to 10 s`).

## For the agent: a section for AGENTS.md or CLAUDE.md

Copy it into the instructions file of your project, and adapt the last step.

```markdown
## Quod: proved functions

When asked to write a function in Quod, or a function that must be proved correct:

1. Read the language reference once with `quod_reference`.
2. Write the function with a contract that determines its result: state what the result is
   (bounds, order, membership...), not how to compute it. Declare an intended freedom with
   `loose`; never weaken a contract to make it pass.
3. Call `quod_check` until the summary starts with `verified`. A counterexample gives inputs
   that break the code or the contract: fix one or the other. When the solver gives up without a
   counterexample, add an `assert`, an invariant or a `lemma` (see the reference).
4. Call `quod_build` and save the Python module next to the code that uses it.
5. Tell me which functions the contracts rely on (the summary lists them under "to review with
   the contracts"), and every `loose`: the proofs show that the code agrees with them, not that
   they say what was meant.
```
