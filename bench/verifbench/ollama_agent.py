"""A minimal coding agent for a local model served by Ollama, talking to `quod mcp`.

VerifBench measures agents of other vendors too; this one needs no account: an open-weight model
(Qwen) on the local machine. It reads the task on stdin and works in the current directory, with
the tools of the Quod MCP server (as the quod-mcp arm gives Claude) plus reading, writing and
listing files. It prints one JSON object, with the fields run.py reads from `claude -p`.

    python -m verifbench.ollama_agent --model qwen2.5-coder:14b < PROMPT.md
"""
from __future__ import annotations

import argparse
import json
import os

import subprocess
import sys
import time
import urllib.request
from pathlib import Path

OLLAMA = os.environ.get("OLLAMA_HOST", "http://localhost:11434")

SYSTEM = (
    "You are a coding agent working in the current directory. Use the tools to read and write files "
    "and to check your work. Call one or more tools in each turn until the task is done; then answer "
    "with a short final message and no tool call."
)

FILE_TOOLS = [
    {"name": "read_file", "description": "Read a text file of the current directory.",
     "inputSchema": {"type": "object", "properties": {"path": {"type": "string"}}, "required": ["path"]}},
    {"name": "write_file", "description": "Write (create or replace) a text file of the current directory.",
     "inputSchema": {"type": "object", "properties": {"path": {"type": "string"}, "content": {"type": "string"}},
                     "required": ["path", "content"]}},
    {"name": "list_files", "description": "List the files of the current directory.",
     "inputSchema": {"type": "object", "properties": {}}},
]


class Mcp:
    """A client of `quod mcp` on stdio, one request at a time."""

    def __init__(self, quod: str):
        self.p = subprocess.Popen([quod, "mcp", "--require-contracts"], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, text=True, encoding="utf-8")
        self.next = 0
        self.request("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                                    "clientInfo": {"name": "verifbench-ollama", "version": "0"}})
        self.p.stdin.write(json.dumps({"jsonrpc": "2.0", "method": "notifications/initialized"}) + "\n")
        self.p.stdin.flush()

    def request(self, method: str, params: dict) -> dict:
        self.next += 1
        self.p.stdin.write(json.dumps({"jsonrpc": "2.0", "id": self.next, "method": method, "params": params}) + "\n")
        self.p.stdin.flush()
        while True:
            message = json.loads(self.p.stdout.readline())
            if message.get("id") == self.next:  # notifications (progress) are skipped
                return message

    def tools(self) -> list[dict]:
        return self.request("tools/list", {})["result"]["tools"]

    def call(self, name: str, arguments: dict) -> str:
        r = self.request("tools/call", {"name": name, "arguments": arguments})
        if "error" in r:
            return "error: " + r["error"]["message"]
        return "\n".join(c.get("text", "") for c in r["result"]["content"])

    def close(self):
        self.p.stdin.close()
        self.p.wait(timeout=30)


def inside(path: str) -> Path:
    """A path of the current directory, never outside it."""
    p = (Path.cwd() / path).resolve()
    if Path.cwd().resolve() not in [p, *p.parents]:
        raise ValueError("only files of the current directory")
    return p


def file_tool(name: str, args: dict) -> str:
    try:
        if name == "read_file":
            return inside(args["path"]).read_text(encoding="utf-8")
        if name == "write_file":
            inside(args["path"]).write_text(args["content"], encoding="utf-8")
            return "written: " + args["path"]
        if name == "list_files":
            return "\n".join(sorted(p.name for p in Path.cwd().iterdir() if p.is_file()))
    except (OSError, KeyError, ValueError) as e:
        return "error: " + str(e)
    return "error: unknown tool " + name


def chat(model: str, messages: list, tools: list, ctx: int) -> dict:
    body = json.dumps({"model": model, "messages": messages, "tools": tools, "stream": False,
                       "options": {"num_ctx": ctx, "temperature": 0.2}}).encode()
    req = urllib.request.Request(OLLAMA + "/api/chat", data=body, headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=900) as r:
        return json.loads(r.read())


def calls_in_text(content: str, names: set[str]) -> list[dict]:
    """Some models write the tool call as JSON in the text instead of a tool_calls field."""
    found = []
    decoder = json.JSONDecoder()
    i = content.find("{")
    while i >= 0:
        try:
            j, end = decoder.raw_decode(content, i)  # one JSON value starting here (several may follow)
        except json.JSONDecodeError:
            i = content.find("{", i + 1)
            continue
        for item in j if isinstance(j, list) else [j]:
            if isinstance(item, dict) and item.get("name") in names:
                found.append({"function": {"name": item["name"], "arguments": item.get("arguments") or {}}})
        i = content.find("{", end)
    return found


def journal(**entry: object) -> None:
    """One line per turn and per tool call on stderr, which run.py keeps as agent_stderr.txt:
    what the model did, to tell a model that does not call the tools from one that misreads
    their answers."""
    print(json.dumps(entry, ensure_ascii=False), file=sys.stderr, flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", required=True)
    ap.add_argument("--quod", default=os.environ.get("QUOD_EXE", "quod"))
    ap.add_argument("--max-turns", type=int, default=40)
    ap.add_argument("--ctx", type=int, default=32768)
    a = ap.parse_args()
    task = sys.stdin.read()
    mcp = Mcp(a.quod)
    specs = FILE_TOOLS + mcp.tools()
    tools = [{"type": "function", "function": {"name": t["name"], "description": t["description"],
                                               "parameters": t["inputSchema"]}} for t in specs]
    names = {t["name"] for t in specs}
    messages = [{"role": "system", "content": SYSTEM}, {"role": "user", "content": task}]
    turns, tokens_in, tokens_out, final, error = 0, 0, 0, "", False
    t0 = time.monotonic()
    try:
        while turns < a.max_turns:
            r = chat(a.model, messages, tools, a.ctx)
            turns += 1
            tokens_in += r.get("prompt_eval_count") or 0
            tokens_out += r.get("eval_count") or 0
            msg = r["message"]
            native = msg.get("tool_calls")
            calls = native or calls_in_text(msg.get("content") or "", names)
            journal(turn=turns, text=(msg.get("content") or "")[:2000], calls=len(calls or []),
                    calls_in_text=bool(calls) and not native)
            messages.append({"role": "assistant", "content": msg.get("content") or "", **({"tool_calls": calls} if calls else {})})
            if not calls:
                final = msg.get("content") or ""
                break
            for c in calls:
                name = c["function"]["name"]
                args = c["function"].get("arguments") or {}
                if isinstance(args, str):
                    try:
                        args = json.loads(args)
                    except json.JSONDecodeError:
                        args = {}
                out = file_tool(name, args) if name in {"read_file", "write_file", "list_files"} \
                    else mcp.call(name, args) if name in names else "error: unknown tool " + name
                messages.append({"role": "tool", "content": out[:20000], "tool_name": name})
                journal(turn=turns, tool=name, args={k: (v if len(str(v)) <= 4000 else str(v)[:4000] + "...")
                                                     for k, v in args.items()} if isinstance(args, dict) else args,
                        out=out[:1500], out_len=len(out))
        else:
            final = "stopped: max turns"
    except Exception as e:  # the run is recorded, not lost
        error, final = True, f"{type(e).__name__}: {e}"
    finally:
        mcp.close()
    print(json.dumps({"type": "result", "is_error": error, "num_turns": turns, "total_cost_usd": 0,
                      "duration_ms": int((time.monotonic() - t0) * 1000), "model": a.model,
                      "usage": {"input_tokens": tokens_in, "output_tokens": tokens_out},
                      "permission_denials": [], "result": final}))


if __name__ == "__main__":
    main()
