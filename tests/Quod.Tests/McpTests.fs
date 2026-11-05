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

/// Check or build with `--require-contracts`, as `quod mcp --require-contracts` does.
let private strictCallWith (extra: string) (tool: string) (program: string) : JsonElement =
    let strict = { settings with RequireContracts = true }
    let arguments = "{" + extra + "\"source\": " + JsonSerializer.Serialize(program) + "}"
    let line =
        "{\"jsonrpc\": \"2.0\", \"id\": 8, \"method\": \"tools/call\", \"params\": {\"name\": \"" + tool
        + "\", \"arguments\": " + arguments + "}}"
    match Quod.Mcp.handle strict line with
    | Some r -> JsonDocument.Parse(r).RootElement.GetProperty("result").GetProperty("structuredContent").Clone()
    | None -> failwith "no response"

let private strictCall = strictCallWith ""

let private verified (r: JsonElement) = r.GetProperty("verified").GetBoolean()

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
let ``progress is told when each step starts and ends, and always grows`` () =
    let told = ResizeArray<float * int * string>()
    match Quod.Pipeline.check "p.quod" clamp { settings with Progress = fun d t what -> told.Add((d, t, what)) } with
    | Quod.Pipeline.Checked _ ->
        let values = [ for (d, _, _) in told -> d ]
        Assert.True(List.pairwise values |> List.forall (fun (a, b) -> b > a), sprintf "%A" values)
        Assert.Equal(2.0, List.last values)
        Assert.All(told, fun (_, t, _) -> Assert.Equal(2, t))
        let (_, _, first) = told.[0]
        Assert.Equal("checking the obligations of clamp", first)
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

// --- --require-contracts ------------------------------------------------------------

/// A statement function without ensures, as Qwen3 wrote max_subarray (run t6-qwen3-30b).
let private noContract =
    "fn f(xs: seq<int>) -> int { let mut n = 0; let mut i = 0; while i < len(xs) invariant 0 <= i <= len(xs) decreases len(xs) - i { n = n + 1; i = i + 1; } return n; }"

[<Fact>]
let ``a statement function without ensures is a warning by default, an error with require-contracts`` () =
    let plain, _ = call "quod_check" (source noContract)
    Assert.True(verified plain)
    let strict = strictCall "quod_check" noContract
    Assert.False(verified strict)
    Assert.Contains("missing (no ensures)", strict.GetProperty("summary").GetString())

[<Fact>]
let ``require-contracts does not build a function without ensures, even with run-time checks`` () =
    let r = strictCallWith "\"runtime_checks\": true, " "quod_build" noContract
    Assert.False(r.GetProperty("built").GetBoolean())
    Assert.Contains("--require-contracts", r.GetProperty("summary").GetString())

[<Fact>]
let ``require-contracts refuses an expression function nothing calls`` () =
    let plain, _ = call "quod_check" (source "fn g(x: int) -> int { x + 1 }")
    Assert.True(verified plain)
    Assert.False(verified (strictCall "quod_check" "fn g(x: int) -> int { x + 1 }"))
    // recursion is not a caller
    let recursive = "fn sum(xs: seq<int>) -> int decreases len(xs) { if len(xs) == 0 { 0 } else { sum(xs[..len(xs) - 1]) + xs[len(xs) - 1] } }"
    Assert.False(verified (strictCall "quod_check" recursive))

[<Fact>]
let ``require-contracts refuses a loose that accepts every result`` () =
    let program = "fn f(x: int) -> int ensures result > x loose (a, b) => true { x + 1 }"
    let plain, _ = call "quod_check" (source program)
    Assert.True(verified plain)
    Assert.False(verified (strictCall "quod_check" program))
    Assert.False((strictCall "quod_build" program).GetProperty("built").GetBoolean())

[<Fact>]
let ``require-contracts refuses a requires that fixes a parameter, not one that relates them`` () =
    let sort = "fn sort(xs: seq<int>) -> seq<int> requires len(xs) == 0 ensures len(result) == len(xs) { xs }"
    Assert.True(verified (fst (call "quod_check" (source sort))))
    let r = strictCall "quod_check" sort
    Assert.False(verified r)
    Assert.Contains("input fixed by its requires", r.GetProperty("summary").GetString())
    Assert.False(verified (strictCall "quod_check" "fn f(x: int) -> int requires x == 5 ensures result == x { x }"))
    Assert.True(verified (strictCall "quod_check" "fn f(x: int, y: int) -> int requires x == y ensures result == x + y { x + y }"))
    Assert.True(verified (strictCall "quod_check" "fn f(xs: seq<int>, n: nat) -> int requires n == len(xs) ensures result == n + 1 { n + 1 }"))
    Assert.True(verified (strictCall "quod_check" "fn f(x: int) -> int requires x > 0 ensures result == x + 1 { x + 1 }"))
    // a fixed length of 2 or more is a record: a colour, a date
    Assert.True(verified (strictCall "quod_check" "fn lum(rgb: seq<int>) -> int requires len(rgb) == 3 ensures result == rgb[0] + rgb[1] + rgb[2] { rgb[0] + rgb[1] + rgb[2] }"))
    Assert.False(verified (strictCall "quod_check" "fn f(xs: seq<int>) -> int requires len(xs) == 1 ensures result == xs[0] { xs[0] }"))

[<Fact>]
let ``require-contracts refuses a contract its requires already gives for an unchanged argument`` () =
    let sort = "fn sort(xs: seq<int>) -> seq<int> requires forall i in 0..len(xs) - 1: xs[i] <= xs[i + 1] ensures result == xs { xs }"
    Assert.True(verified (fst (call "quod_check" (source sort))))
    let r = strictCall "quod_check" sort
    Assert.False(verified r)
    Assert.Contains("already guaranteed by its requires", r.GetProperty("summary").GetString())
    Assert.False(verified (strictCall "quod_check" "fn f(x: int) -> int requires x > 0 ensures result == x { x }"))
    // a requires that a real function needs
    Assert.True(verified (strictCall "quod_check" "fn inc(x: int) -> int requires x > 0 ensures result == x + 1 { x + 1 }"))

[<Fact>]
let ``quod contract evaluates a contract on given arguments and results`` () =
    let src = "fn f(x: int) -> int requires x > 0 ensures result == x + 1 { x + 1 }"
    match Quod.Mcp.contractCases "p.quod" src "f" "[{\"args\": [2], \"results\": [3, 4]}, {\"args\": [-1], \"results\": [0]}]" with
    | Ok text -> Assert.Equal("[{\"requires\":true,\"results\":[true,false]},{\"requires\":false,\"results\":[true]}]", text)
    | Result.Error why -> failwith why

[<Fact>]
let ``require-contracts refuses a lemma written as a function`` () =
    let lemma = "fn fact(x: int) -> bool ensures result ensures x + 1 > x { return true; }"
    Assert.True(verified (fst (call "quod_check" (source lemma))))
    Assert.False(verified (strictCall "quod_check" lemma))

[<Fact>]
let ``each loose shows two results it accepts`` () =
    let program = "fn f(x: int) -> int ensures result >= 0 loose (a, b) => a + b >= 0 { if x > 0 { x } else { 0 } }"
    let r, _ = call "quod_check" (source program)
    let summary = r.GetProperty("summary").GetString()
    Assert.Contains("loose: f (x = ", summary)
    Assert.Contains(" or ", summary)

[<Fact>]
let ``quod_build generates C# on request, and refuses an unknown target`` () =
    let args = "{\"target\": \"csharp\", \"namespace\": \"Acme.Rules\", \"source\": " + JsonSerializer.Serialize(clamp) + "}"
    let r, _ = call "quod_build" args
    Assert.True(r.GetProperty("built").GetBoolean())
    Assert.Equal("csharp", r.GetProperty("language").GetString())
    Assert.Contains("namespace Acme.Rules", r.GetProperty("code").GetString())
    let bad = request 9 "tools/call" ("{\"name\": \"quod_build\", \"arguments\": {\"target\": \"cobol\", \"source\": " + JsonSerializer.Serialize(clamp) + "}}")
    Assert.True(bad.GetProperty("result").GetProperty("isError").GetBoolean())

[<Fact>]
let ``the reference served to agents has no solution of a task`` () =
    let all, _ = call "quod_reference" "{}"
    let text = all.GetProperty("reference").GetString()
    for task in [ "binary_search"; "merge_intervals"; "rle_encode"; "bounded_queue"; "max_subarray"; "rotate"
                  "gcd"; "merge_sorted"; "majority_element"; "transpose"; "next_permutation"; "two_sum_sorted" ] do
        Assert.DoesNotContain("fn " + task + "(", text)

[<Fact>]
let ``require-contracts keeps the expression functions a contract is stated with`` () =
    let program =
        "fn sum(xs: seq<int>) -> int decreases len(xs) { if len(xs) == 0 { 0 } else { sum(xs[..len(xs) - 1]) + xs[len(xs) - 1] } }\n"
        + "fn total(xs: seq<int>) -> int ensures result == sum(xs) {\n"
        + "  let mut s = 0; let mut i = 0;\n"
        + "  while i < len(xs) invariant 0 <= i <= len(xs) invariant s == sum(xs[..i]) decreases len(xs) - i { s = s + xs[i]; i = i + 1; }\n"
        + "  return s; }"
    Assert.True(verified (strictCall "quod_check" program))
    Assert.True(verified (strictCall "quod_check" clamp))

/// --smt-log is what z3 received: replayed on a new z3, it gives the answers it records.
[<Fact>]
let ``the smt log replays to the answers it records`` () =
    let src = "fn f(a: int) -> int\n  ensures result >= a\n{\n  a\n}\n"
    let log = System.IO.Path.GetTempFileName()
    try
        Quod.Pipeline.check "p.quod" src { settings with SmtLog = Some log } |> ignore
        let lines = System.IO.File.ReadAllLines log
        Assert.Contains(lines, fun l -> l.StartsWith "(get-value")
        let recorded =
            lines |> Array.filter (fun l -> l.StartsWith "; answer: ")
            |> Array.map (fun l -> (l.Substring 10).Split(' ').[0])
        Assert.NotEmpty recorded
        let psi = System.Diagnostics.ProcessStartInfo(z3Path, "-smt2 \"" + log + "\"")
        psi.RedirectStandardOutput <- true
        psi.UseShellExecute <- false
        use z3 = System.Diagnostics.Process.Start psi
        let out = z3.StandardOutput.ReadToEnd()
        z3.WaitForExit()
        let replayed =
            out.Split('\n') |> Array.map (fun l -> l.Trim())
            |> Array.filter (fun l -> l = "sat" || l = "unsat" || l = "unknown")
        Assert.Equal<string[]>(recorded, replayed)
    finally
        System.IO.File.Delete log
