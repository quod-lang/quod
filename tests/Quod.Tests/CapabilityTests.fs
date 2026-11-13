module Quod.Tests.CapabilityTests

open System
open System.IO
open Xunit
open Quod.Diagnostics
open Quod.Pipeline
open Quod.Tests.VerifyTests

let private settings = { defaultSettings with Z3 = Some z3Path }

/// Check `main.quod`, written to a directory of its own (the standard library is embedded).
let private withMain (src: string) (use': string -> Outcome -> unit) =
    let dir = Path.Combine(Path.GetTempPath(), "quod-cap-" + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory dir |> ignore
    try
        let main = Path.Combine(dir, "main.quod")
        File.WriteAllText(main, src)
        use' dir (check main src settings)
    finally
        Directory.Delete(dir, true)

let private rejected (expected: string) (src: string) =
    withMain src (fun _ outcome ->
        match outcome with
        | Rejected ds -> Assert.True(ds |> List.exists (fun d -> d.Message.Contains expected), "no error with '" + expected + "' in: " + String.Join(" | ", ds |> List.map (fun d -> d.Message)))
        | Checked(_, r) -> failwithf "expected a rejection with '%s', got: %s" expected (String.Join(" | ", errorsOf r |> List.map (fun d -> d.Message)))
        | other -> failwithf "%A" other)

let private verified (src: string) =
    withMain src (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.Empty(errorsOf r)
        | Rejected ds -> failwithf "%s" (String.Join(" | ", ds |> List.map (fun d -> d.Message)))
        | other -> failwithf "%A" other)

let private hello =
    "import console\n\nfn greet(c: console.Console, name: string) -> console.Console\n"
    + "  ensures console.written(result) == console.written(c) + [\"hello, \" + name]\n{\n  console.say(c, \"hello, \" + name)\n}\n"

[<Fact>]
let ``a function that writes through a console is proved from the model`` () =
    verified hello

[<Fact>]
let ``a contract that says only how many lines are written is refused as incomplete`` () =
    withMain "import console\n\nfn one(c: console.Console) -> console.Console\n  ensures len(console.written(result)) == len(console.written(c)) + 1\n{\n  console.say(c, \"a\")\n}\n" (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.True(errorsOf r |> List.exists (fun d -> d.Message.Contains "two different results"))
        | other -> failwithf "%A" other)

[<Fact>]
let ``a console is used once`` () =
    rejected "has already been used" "import console\n\nfn bad(c: console.Console) -> console.Console {\n  let a = console.say(c, \"x\");\n  console.say(c, \"y\")\n}\n"
    rejected "has already been used" "import console\n\nfn bad(c: console.Console) -> (console.Console, console.Console) {\n  (c, c)\n}\n"

[<Fact>]
let ``the console that a call returns can be used, once more`` () =
    verified "import console\n\nfn ok(c: console.Console) -> console.Console\n  ensures console.written(result) == console.written(c) + [\"a\", \"b\"]\n{\n  let d = console.say(c, \"a\");\n  console.say(d, \"b\")\n}\n"

[<Fact>]
let ``both branches of an if may use the console`` () =
    verified "import console\n\nfn pick(c: console.Console, b: bool) -> console.Console\n  ensures console.written(result) == console.written(c) + [if b { \"yes\" } else { \"no\" }]\n{\n  if b { console.say(c, \"yes\") } else { console.say(c, \"no\") }\n}\n"
    rejected "has already been used" "import console\n\nfn bad(c: console.Console, b: bool) -> console.Console {\n  let d = if b { console.say(c, \"yes\") } else { c };\n  console.say(c, \"again\")\n}\n"

[<Fact; Trait("Category", "Slow")>]
let ``a loop that writes hands the console back at the end of each turn`` () =
    let loop (invariants: string) (step: string) =
        "import console\n\nfn lines(c: console.Console, n: nat) -> console.Console\n"
        + "  ensures len(console.written(result)) == len(console.written(c)) + n\n"
        + "  ensures forall i in 0..len(console.written(c)): console.written(result)[i] == console.written(c)[i]\n"
        + "  ensures forall i in 0..n: console.written(result)[len(console.written(c)) + i] == \"line\"\n"
        + "  ensures console.pending(result) == console.pending(c)\n{\n"
        + "  let mut d = c;\n  let mut i: nat = 0;\n  while i < n\n    invariant 0 <= i && i <= n\n" + invariants + "    decreases n - i\n  {\n"
        + step + "    i = i + 1;\n  }\n  return d;\n}\n"
    let invariants =
        "    invariant len(console.written(d)) == len(console.written(c)) + i\n"
        + "    invariant forall j in 0..len(console.written(c)): console.written(d)[j] == console.written(c)[j]\n"
        + "    invariant forall j in 0..i: console.written(d)[len(console.written(c)) + j] == \"line\"\n"
        + "    invariant console.pending(d) == console.pending(c)\n"
    verified (loop invariants "    d = console.say(d, \"line\");\n")
    rejected "does not hand it back" (loop "" "    let e = console.say(d, \"line\");\n")

[<Fact>]
let ``a program cannot build a console, nor read it in code, nor keep it in a collection`` () =
    rejected "cannot be built" "import console\n\nfn bad(c: console.Console) -> console.Console {\n  console.Console([], [])\n}\n"
    rejected "code cannot read" "import console\n\nfn peek(c: console.Console) -> seq<string> {\n  console.written(c)\n}\n"
    rejected "cannot be put in a sequence" "import console\n\nfn keep(c: console.Console) -> seq<console.Console> {\n  [c]\n}\n"

[<Fact>]
let ``a function without a console cannot reach one`` () =
    // no ambient authority: `say` needs a Console, and there is no way to get one but to receive it
    rejected "" "import console\n\nfn bad() -> int {\n  console.say(console.Console([]), \"x\");\n  1\n}\n"

[<Fact>]
let ``the generated Python writes the lines, and the generated C# carries the console`` () =
    withMain hello (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            let file = Path.Combine(dir, "main.quod")
            match generate (Python false) file typed r false with
            | Result.Error why -> failwith why
            | Ok g ->
                File.WriteAllText(Path.Combine(dir, "main.py"), g.Code)
                for m, text in g.Imported do File.WriteAllText(Path.Combine(dir, m + ".py"), text)
                let psi = Diagnostics.ProcessStartInfo("python", "-c \"import io, main, console; s = io.StringIO(); c = console.Console(s); r = main.greet(c, 'Ada'); print(repr(s.getvalue()), r is c)\"")
                psi.WorkingDirectory <- dir
                psi.RedirectStandardOutput <- true
                psi.RedirectStandardError <- true
                psi.UseShellExecute <- false
                use p = Diagnostics.Process.Start psi
                let out = p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd()
                p.WaitForExit()
                Assert.Equal("'hello, Ada\\n' True", out.Trim())
            match generate (CSharp Quod.CodegenCSharp.defaultOptions) file typed r false with
            | Result.Error why -> failwith why
            | Ok g ->
                Assert.Contains("ConsoleModule.Console Greet(ConsoleModule.Console c, string name)", g.Code)
                let runtime = g.Imported |> List.find (fun (m, _) -> m = "console") |> snd
                Assert.Contains("public Console(TextWriter output)", runtime)
        | other -> failwithf "%A" other)

[<Fact>]
let ``lines of a real length are proved as fast as short ones`` () =
    // a literal was a chain of concatenations: from 17 characters on, this took 25 s or timed out
    let clock = Diagnostics.Stopwatch.StartNew()
    verified "import console\n\nfn main(c: console.Console) -> console.Console\n  ensures console.written(result) == console.written(c) + [\"Hello from Quod, a first line\", \"and a second line of a fair length\"]\n  ensures console.pending(result) == console.pending(c)\n{\n  let a = console.say(c, \"Hello from Quod, a first line\");\n  console.say(a, \"and a second line of a fair length\")\n}\n"
    Assert.True(clock.Elapsed.TotalSeconds < 15.0, "took " + string clock.Elapsed.TotalSeconds + " s")

[<Fact>]
let ``a long string literal means what it says`` () =
    verified "fn ne() -> bool\n  ensures result == false\n{\n  \"abcdefghijklmnop\" == \"abcdefghijklmnoq\"\n}\n\nfn size() -> nat\n  ensures result == 16\n{\n  len(\"abcdefghijklmnop\")\n}\n\nfn at() -> char\n  ensures result == 'd'\n{\n  \"abcdefghijklmnop\"[3]\n}\n"
    withMain "fn bad() -> bool\n  ensures result == true\n{\n  \"abcdefghijklmnop\" == \"abcdefghijklmnoq\"\n}\n" (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.True(errorsOf r |> List.exists (fun d -> d.Kind = "proof"))
        | other -> failwithf "%A" other)

// --- reading ---------------------------------------------------------------------------------------

let private echo =
    "import console\nimport option\n\nfn main(c: console.Console) -> console.Console\n"
    + "  ensures len(console.pending(c)) == 0 ==> console.written(result) == console.written(c) + [\"nothing to read\"] && console.pending(result) == console.pending(c)\n"
    + "  ensures len(console.pending(c)) > 0 ==> console.written(result) == console.written(c) + [\"you said: \" + console.pending(c)[0]] && console.pending(result) == console.pending(c)[1..]\n"
    + "{\n  let r = console.read_line(c);\n  let d = r.0;\n  match r.1 {\n    None => console.say(d, \"nothing to read\"),\n    Some(line) => console.say(d, \"you said: \" + line),\n  }\n}\n"

[<Fact>]
let ``a program that reads is proved from the model of what is left to read`` () =
    verified echo

[<Fact>]
let ``what read_line returns is read once, and the console it returns is used once`` () =
    // both parts of the pair are used, each once
    verified ("import console\nimport option\n\nfn f(c: console.Console) -> (console.Console, option.Option<string>)\n  ensures result.0 == result.0\n{\n  let r = console.read_line(c);\n  (r.0, r.1)\n}\n" |> fun s -> s.Replace("  ensures result.0 == result.0\n", ""))
    rejected "has already been used" "import console\nimport option\n\nfn f(c: console.Console) -> console.Console {\n  let r = console.read_line(c);\n  let a = console.say(r.0, \"x\");\n  console.say(r.0, \"y\")\n}\n"
    rejected "has already been used" "import console\nimport option\n\nfn f(c: console.Console) -> console.Console {\n  let r = console.read_line(c);\n  console.say(c, \"x\")\n}\n"

[<Fact>]
let ``code cannot read what is left to read`` () =
    rejected "code cannot read" "import console\n\nfn f(c: console.Console) -> seq<string> {\n  console.pending(c)\n}\n"

[<Fact>]
let ``the generated Python reads the lines it is given`` () =
    withMain echo (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (Python false) (Path.Combine(dir, "main.quod")) typed r false with
            | Result.Error why -> failwith why
            | Ok g ->
                File.WriteAllText(Path.Combine(dir, "main.py"), g.Code)
                for m, text in g.Imported do File.WriteAllText(Path.Combine(dir, m + ".py"), text)
                let driver =
                    [ "import io, main, console"
                      "a = console.Console(io.StringIO(), io.StringIO('one\\ntwo\\n'))"
                      "main.main(a)"
                      "b = console.Console(io.StringIO(), io.StringIO(''))"
                      "main.main(b)"
                      "print(repr(a._stream.getvalue()), repr(b._stream.getvalue()))" ]
                File.WriteAllText(Path.Combine(dir, "driver.py"), String.Join("\n", driver))
                let psi = Diagnostics.ProcessStartInfo("python", "driver.py")
                psi.WorkingDirectory <- dir
                psi.RedirectStandardOutput <- true
                psi.RedirectStandardError <- true
                psi.UseShellExecute <- false
                use p = Diagnostics.Process.Start psi
                let out = p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd()
                p.WaitForExit()
                Assert.Equal("'you said: one\\n' 'nothing to read\\n'", out.Trim())
            match generate (CSharp Quod.CodegenCSharp.defaultOptions) (Path.Combine(dir, "main.quod")) typed r false with
            | Result.Error why -> failwith why
            | Ok g ->
                let runtime = g.Imported |> List.find (fun (m, _) -> m = "console") |> snd
                Assert.Contains("ReadLine(Console c)", runtime)
                Assert.True(g.Imported |> List.exists (fun (m, _) -> m = "option"))
        | other -> failwithf "%A" other)
