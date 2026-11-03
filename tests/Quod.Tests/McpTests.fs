module Quod.Tests.McpTests

open System.Text.Json
open Xunit
open Quod.Tests.VerifyTests

let private settings = { Quod.Pipeline.defaultSettings with Z3 = Some z3Path }

/// Send one request to the server; the parsed response.
let private request (id: int) (method': string) (params': string) : JsonElement =
    let line = "{\"jsonrpc\": \"2.0\", \"id\": " + string id + ", \"method\": \"" + method' + "\", \"params\": " + params' + "}"
    match Quod.Mcp.handle settings line with
    | Some r -> JsonDocument.Parse(r).RootElement
    | None -> failwith "no response"

/// Call a tool; its structured result and its text.
let private call (tool: string) (arguments: string) : JsonElement * string =
    let r = request 7 "tools/call" ("{\"name\": \"" + tool + "\", \"arguments\": " + arguments + "}")
    let result = r.GetProperty "result"
    Assert.False(result.GetProperty("isError").GetBoolean(), result.GetProperty("content").[0].GetProperty("text").GetString())
    result.GetProperty "structuredContent", result.GetProperty("content").[0].GetProperty("text").GetString()

let private source (program: string) = "{\"source\": " + JsonSerializer.Serialize(program) + "}"

let private clamp =
    "fn clamp(x: int, lo: int, hi: int) -> int\n  requires lo <= hi\n  ensures lo <= result <= hi\n"
    + "  ensures x < lo ==> result == lo\n  ensures x > hi ==> result == hi\n  ensures lo <= x <= hi ==> result == x\n"
    + "{\n  if x < lo { lo } else if x > hi { hi } else { x }\n}\n"

let private weak = "fn clamp(x: int, lo: int, hi: int) -> int requires lo <= hi ensures lo <= result <= hi { if x < lo { lo } else if x > hi { hi } else { x } }"

let private withArgs (program: string) (rest: string) =
    let s = source program
    s.Substring(0, s.Length - 1) + ", " + rest + "}"

[<Fact>]
let ``initialize answers with the protocol version asked for, and four tools are listed`` () =
    let r = request 1 "initialize" "{\"protocolVersion\": \"2025-03-26\", \"capabilities\": {}, \"clientInfo\": {\"name\": \"t\", \"version\": \"0\"}}"
    let result = r.GetProperty "result"
    Assert.Equal("2025-03-26", result.GetProperty("protocolVersion").GetString())
    Assert.Equal("quod", result.GetProperty("serverInfo").GetProperty("name").GetString())
    let tools = (request 2 "tools/list" "{}").GetProperty("result").GetProperty("tools")
    Assert.Equal<string list>([ "quod_check"; "quod_build"; "quod_run"; "quod_reference" ], [ for t in tools.EnumerateArray() -> t.GetProperty("name").GetString() ])

[<Fact>]
let ``a notification gets no response, a bad message a parse error`` () =
    Assert.Equal(None, Quod.Mcp.handle settings "{\"jsonrpc\": \"2.0\", \"method\": \"notifications/initialized\"}")
    let r = JsonDocument.Parse((Quod.Mcp.handle settings "{not json").Value).RootElement
    Assert.Equal(-32700, r.GetProperty("error").GetProperty("code").GetInt32())

[<Fact>]
let ``quod_check verifies a program, and rejects an underspecified one with a witness`` () =
    let ok, text = call "quod_check" (source clamp)
    Assert.True(ok.GetProperty("verified").GetBoolean(), text)
    Assert.StartsWith("verified:", text)
    let bad, _ = call "quod_check" (source weak)
    Assert.False(bad.GetProperty("verified").GetBoolean())
    let d = bad.GetProperty("diagnostics").EnumerateArray() |> Seq.find (fun d -> d.GetProperty("kind").GetString() = "completeness")
    Assert.Equal("underspecified", d.GetProperty("status").GetString())
    Assert.True(d.GetProperty("witness").TryGetProperty("result_a") |> fst)

[<Fact>]
let ``quod_build returns the Python module, and builds nothing from an underspecified program`` () =
    let built, _ = call "quod_build" (source clamp)
    Assert.True(built.GetProperty("built").GetBoolean())
    Assert.Contains("def clamp(", built.GetProperty("code").GetString())
    let refused, _ = call "quod_build" (source weak)
    Assert.False(refused.GetProperty("built").GetBoolean())

[<Fact>]
let ``quod_run gives the result, the obligation that fails, or the requires that does not hold`` () =
    let r, text = call "quod_run" (withArgs clamp "\"function\": \"clamp\", \"args\": [15, 0, 10]")
    Assert.Equal("ok", r.GetProperty("status").GetString())
    Assert.Equal(10, r.GetProperty("result").GetInt32())
    Assert.Equal("clamp returns 10", text)
    let req, _ = call "quod_run" (withArgs clamp "\"function\": \"clamp\", \"args\": [1, 5, 0]")
    Assert.Equal("requires-false", req.GetProperty("status").GetString())
    let buggy = "fn last(xs: seq<int>) -> int requires len(xs) > 0 { xs[len(xs)] }"
    let v, _ = call "quod_run" (withArgs buggy "\"function\": \"last\", \"args\": [[1, 2, 3]]")
    Assert.Equal("violation", v.GetProperty("status").GetString())
    Assert.Equal("index in bounds", v.GetProperty("property").GetString())

[<Fact>]
let ``quod_reference gives the language reference, or one section of it`` () =
    let all, _ = call "quod_reference" "{}"
    Assert.Contains("## The language", all.GetProperty("reference").GetString())
    let one, text = call "quod_reference" "{\"section\": \"Hints and lemmas\"}"
    Assert.StartsWith("### Hints and lemmas", text)
    Assert.DoesNotContain("## Completeness", one.GetProperty("reference").GetString())
    let r = request 9 "tools/call" "{\"name\": \"quod_reference\", \"arguments\": {\"section\": \"no such thing\"}}"
    Assert.True(r.GetProperty("result").GetProperty("isError").GetBoolean())

[<Fact>]
let ``a cancelled check stops at once: z3 is killed`` () =
    // test of 0.1.1: a cancelled call ran to its end; quod mcp now cancels it (notifications/cancelled)
    let slow = String.concat "\n" [ for k in 0 .. 7 -> "fn f" + string k + "(a: int) -> int requires a > 0 ensures result == 0 { (a * a * a - a + 6 * " + string k + ") % 6 }" ]
    use cts = new System.Threading.CancellationTokenSource()
    cts.CancelAfter 1000
    let clock = System.Diagnostics.Stopwatch.StartNew()
    match Quod.Pipeline.check "slow.quod" slow { settings with Cancel = cts.Token } with
    | Quod.Pipeline.Failure(message, _) -> Assert.Contains("cancelled", message)
    | _ -> failwith "expected the check to be cancelled"
    Assert.True(clock.Elapsed.TotalSeconds < 5.0, "cancelled after " + string clock.Elapsed.TotalSeconds + " s")

[<Fact>]
let ``progress is told after each function`` () =
    let told = ResizeArray<int * int>()
    match Quod.Pipeline.check "p.quod" clamp { settings with Progress = fun d t _ -> told.Add((d, t)) } with
    | Quod.Pipeline.Checked _ -> Assert.Equal<(int * int) list>([ 1, 2; 2, 2 ], List.ofSeq told)
    | _ -> failwith "expected a check"

[<Fact>]
let ``a broken postcondition in quod_run comes with the value returned and the clause`` () =
    // test of 0.1.1: the agent had to reread the source to know what was expected
    let add = "fn add(a: int, b: int) -> int ensures result == a + b { if a == b * b * b && b > 2 { return a + b + 1; } return a + b; }"
    let r, text = call "quod_run" (withArgs add "\"function\": \"add\", \"args\": [27, 3]")
    Assert.Equal("violation", r.GetProperty("status").GetString())
    Assert.Equal(31, r.GetProperty("returned").GetInt32())
    Assert.Equal("result == a + b", r.GetProperty("text").GetString())
    Assert.Contains("add(27, 3) returned 31, but postcondition (ensures #1) fails: `result == a + b`", text)

[<Fact>]
let ``the reference served to agents has no vocabulary of the design documents`` () =
    let all, _ = call "quod_reference" "{}"
    let text = all.GetProperty("reference").GetString()
    Assert.DoesNotContain("pillar", text)
    Assert.DoesNotContain("principle 2", text)
    Assert.Contains("## Completeness, built in", text)
