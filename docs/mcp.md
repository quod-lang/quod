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
| `quod_run` | Runs one function on given arguments (JSON numbers, booleans, arrays), checking every assertion, invariant, bound and contract on the way. Returns the result, or the obligation that fails. |
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

`path` arguments are relative to the server's working directory: the one the client starts it in,
usually the project.

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
