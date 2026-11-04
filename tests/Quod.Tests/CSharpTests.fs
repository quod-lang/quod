module Quod.Tests.CSharpTests

open System
open System.Diagnostics
open System.IO
open System.Numerics
open System.Text
open Xunit
open Quod.Typed
open Quod.Eval
open Quod.CodegenCSharp
open Quod.Tests.CodegenTests

let private repoRoot =
    let rec up (d: DirectoryInfo) =
        if Directory.Exists(Path.Combine(d.FullName, "bench", "quod")) then d.FullName else up d.Parent
    up (DirectoryInfo AppContext.BaseDirectory)

let private typedOf (src: string) =
    let typed, errs = Quod.Typecheck.check "p.quod" (Quod.Parser.parseProgram "p.quod" src)
    Assert.True(errs.IsEmpty, "type errors: " + String.concat " | " (errs |> List.map (fun d -> d.Message)))
    typed

let rec private csLiteral (t: Ty) (v: Value) =
    match t, v with
    | _, VInt n -> "new BigInteger(" + n.ToString() + ")"
    | _, VBool b -> if b then "true" else "false"
    | TySeq e, VSeq xs -> "new " + csType e + "[] { " + (xs |> List.map (csLiteral e) |> String.concat ", ") + " }"
    | TyTuple ts, VTuple xs -> "(" + (List.map2 csLiteral ts xs |> String.concat ", ") + ")"
    | _ -> failwith "a value that does not fit its type"

let private runner =
    "using System;\nusing System.Collections;\nusing System.Collections.Generic;\nusing System.Numerics;\nusing System.Runtime.CompilerServices;\n\n"
    + "static class Runner\n{\n"
    + "    static string Show(object v)\n    {\n"
    + "        if (v is bool) return (bool)v ? \"true\" : \"false\";\n"
    + "        if (v is ITuple) { var t = (ITuple)v; var ps = new string[t.Length]; for (int i = 0; i < t.Length; i++) ps[i] = Show(t[i]); return \"(\" + string.Join(\", \", ps) + \")\"; }\n"
    + "        if (v is IEnumerable) { var ps = new System.Collections.Generic.List<string>(); foreach (var x in (IEnumerable)v) ps.Add(Show(x)); return \"[\" + string.Join(\", \", ps) + \"]\"; }\n"
    + "        return v.ToString();\n    }\n\n"
    + "    static void Case(string label, Func<object> f)\n    {\n"
    + "        string text;\n"
    + "        try { text = Show(f()); } catch (Exception e) { text = \"!\" + e.GetType().Name; }\n"
    + "        Console.WriteLine(label + \"\\t\" + text);\n    }\n\n"
    + "    static void Main()\n    {\n"

/// Compile the generated classes and the calls into one program, and run it: label -> what it printed.
let private buildAndRunWith (defines: string) (framework: string) (sources: (string * string) list) (calls: string list) : Map<string, string> =
    let dir = Directory.CreateTempSubdirectory("quod-cs-").FullName
    try
        // C# 7.3 is what .NET Framework has: the code must compile with it on every target
        File.WriteAllText(
            Path.Combine(dir, "T.csproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><OutputType>Exe</OutputType><TargetFramework>" + framework
            + "</TargetFramework><LangVersion>7.3</LangVersion><TreatWarningsAsErrors>true</TreatWarningsAsErrors>"
            + "<InvariantGlobalization>true</InvariantGlobalization><EnableDefaultCompileItems>true</EnableDefaultCompileItems>"
            + "<DefineConstants>$(DefineConstants);" + defines + "</DefineConstants></PropertyGroup>\n"
            + (if framework = "net472" then "  <ItemGroup><Reference Include=\"System.Numerics\" /></ItemGroup>\n" else "")
            + "</Project>\n")
        for name, code in sources do File.WriteAllText(Path.Combine(dir, name), code)
        File.WriteAllText(Path.Combine(dir, "Runner.cs"), runner + String.concat "\n" calls + "\n    }\n}\n")
        let run (exe: string) (args: string) =
            let psi = ProcessStartInfo(exe, args, WorkingDirectory = dir, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false)
            psi.Environment.["DOTNET_CLI_UI_LANGUAGE"] <- "en"
            use p = Process.Start psi
            let err = p.StandardError.ReadToEndAsync()
            let out = p.StandardOutput.ReadToEnd()
            p.WaitForExit()
            p.ExitCode, out + err.Result
        let code, log = run "dotnet" "build -c Release --nologo -v q -o out"
        Assert.True((code = 0), "the generated C# does not compile:\n" + log)
        let exe = Path.Combine(dir, "out", (if OperatingSystem.IsWindows() then "T.exe" else "T"))
        let code, out = run exe ""
        Assert.True((code = 0), "the program failed:\n" + out)
        out.Replace("\r\n", "\n").Split('\n', StringSplitOptions.RemoveEmptyEntries)
        |> Array.map (fun l -> let k = l.IndexOf '\t' in l.Substring(0, k), l.Substring(k + 1))
        |> Map.ofArray
    finally
        try Directory.Delete(dir, true) with _ -> ()

let private buildAndRun = buildAndRunWith ""

let private generated (index: int) (src: string) (checks: Set<string>) (allRequires: bool) =
    let options = { Namespace = "T" + string index; CheckAllRequires = allRequires }
    match generate "p.quod" (typedOf src) checks options with
    | Ok code -> "P" + string index + ".g.cs", code
    | Result.Error why -> failwith why

/// The programs of the repository: inputs drawn as for Python, results compared with the evaluator.
let private repoPrograms =
    lazy
        (let bench = [ "binary_search"; "bounded_queue"; "max_subarray"; "merge_intervals"; "rle_encode"; "rotate" ]
         [ for t in bench -> File.ReadAllText(Path.Combine(repoRoot, "bench", "quod", t, "solution.quod"))
           yield File.ReadAllText(Path.Combine(repoRoot, "examples", "binary_search.quod"))
           yield File.ReadAllText(Path.Combine(repoRoot, "examples", "prefix_sums.quod"))
           // what the checks of the language need to get right, whatever the programs above do
           yield
               "fn nested(a: seq<(int, seq<int>)>, b: seq<(int, seq<int>)>) -> bool { a == b }\n"
               + "fn arith(a: int, b: int) -> (int, int) requires b != 0 { (a / b, a % b) }\n"
               + "fn slices(xs: seq<int>, k: nat) -> seq<int> requires k <= len(xs) { xs[k..] + xs[..k] }\n"
               + "fn build(n: nat) -> seq<int> { let mut r: seq<int> = []; let mut i = 0; while i < n invariant 0 <= i && i <= n decreases n - i { r = r + [i]; i = i + 1; } return r; }\n" ])

let private differentialOn (framework: string) =
    let rnd = Random 20261104
    let sources = ResizeArray()
    let calls = ResizeArray()
    let expected = ResizeArray()
    for i, src in List.indexed repoPrograms.Value do
        let typed = typedOf src
        sources.Add(generated i src Set.empty false)
        let ev = Evaluator(typed.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList)
        for f in typed.Fns |> List.filter (fun f -> not f.IsLemma) do
            let mutable found, tries = 0, 0
            while found < 15 && tries < 3000 do
                tries <- tries + 1
                let args = f.Params |> List.map (fun p -> randomValue rnd p.Ty)
                let env = List.map2 (fun (p: TParam) a -> p.Name, a) f.Params args |> Map.ofList
                if f.Requires |> List.forall (fun r -> ev.Holds(r, env) = Some true) then
                    found <- found + 1
                    let result = try Some(ev.Run(f, args)) with _ -> None
                    match result with
                    | Some value ->
                        let label = "p" + string i + "." + f.Name + "." + string found
                        let literals = List.map2 (fun (p: TParam) a -> csLiteral p.Ty a) f.Params args |> String.concat ", "
                        calls.Add("        Case(\"" + label + "\", () => T" + string i + ".P." + pascal f.Name + "(" + literals + "));")
                        expected.Add((label, valueText value))
                    | None -> ()
    Assert.True(expected.Count > 100, "too few cases: " + string expected.Count)
    let got = buildAndRun framework (List.ofSeq sources) (List.ofSeq calls)
    for label, value in expected do
        Assert.Equal(value, got.[label])

[<Fact>]
let ``the programs of the repository run in C# as in the evaluator`` () = differentialOn "net10.0"

[<Fact>]
let ``they do on .NET Framework 4.7.2 too, where it can be built`` () =
    let pack = @"C:\Program Files (x86)\Reference Assemblies\Microsoft\Framework\.NETFramework\v4.7.2"
    if OperatingSystem.IsWindows() && Directory.Exists pack then differentialOn "net472"

let private traps =
    lazy
        (let unchecked' =
            "fn class(string: int, params: int) -> int { let object = string + params; return object; }\n"
            + "fn scopes(c: bool) -> int { if c { let x = 1; } let x = 2; return x; }\n"
            + "fn forall_then_let(xs: seq<int>) -> int requires forall i in 0..len(xs): xs[i] > 0 { let i = 7; return i; }\n"
            + "fn empty_tuples() -> seq<(int, int)> { [] }\n"
            + "fn nested_empty(xs: seq<seq<int>>) -> seq<seq<int>> { [[]] + xs }\n"
            + "fn len_of(xs: seq<int>) -> int { len(xs) }\n"
            + "fn empty_arg() -> int { len_of([]) }\n"
            + "fn huge() -> int { 123456789012345678901234567890 }\n"
            + "fn down(n: nat) -> int decreases n { if n == 0 { 0 } else { down(n - 1) } }\n"
            + "fn need(x: int) -> int requires x > 0 { x }\n"
            + "fn sorted_only(xs: seq<int>) -> int requires forall i in 0..len(xs) - 1: xs[i] <= xs[i + 1] { len(xs) }\n"
            + "fn eq_seq(a: seq<int>, b: seq<int>) -> bool { a == b }\n"
            + "fn nested_ints(xs: seq<(int, seq<int>)>) -> seq<(int, seq<int>)> { xs + xs[..1] }\n"
            + "fn search(xs: seq<int>, x: int) -> int { let mut i = 0; while i < len(xs) invariant 0 <= i && i <= len(xs) decreases len(xs) - i { if xs[i] == x { return i; } i = i + 1; } return -1; }\n"
         let checked' = "fn wrong(x: int) -> int ensures result > x { return x; }\nfn out_of_bounds(xs: seq<int>) -> int { return xs[3]; }\n"
         let big n = "new BigInteger(" + string n + ")"
         let arr (xs: int list) = "new BigInteger[] { " + (xs |> List.map big |> String.concat ", ") + " }"
         buildAndRun "net10.0"
             [ generated 0 unchecked' Set.empty false
               generated 1 checked' (set [ "wrong"; "out_of_bounds" ]) false
               generated 2 unchecked' Set.empty true ]
             [ "        Case(\"keywords\", () => T0.P.Class(" + big 2 + ", " + big 3 + "));"
               "        Case(\"scopes\", () => T0.P.Scopes(true));"
               "        Case(\"lambda then let\", () => T2.P.ForallThenLet(" + arr [ 1 ] + "));"
               "        Case(\"empty tuples\", () => T0.P.EmptyTuples());"
               "        Case(\"nested empty\", () => T0.P.NestedEmpty(new System.Collections.Generic.IReadOnlyList<BigInteger>[] { " + arr [ 1 ] + " }));"
               "        Case(\"empty arg\", () => T0.P.EmptyArg());"
               "        Case(\"huge\", () => T0.P.Huge());"
               "        Case(\"deep\", () => T0.P.Down(" + big 100000000 + "));"
               "        Case(\"requires\", () => T0.P.Need(" + big -1 + "));"
               "        Case(\"null\", () => T0.P.LenOf((IReadOnlyList<BigInteger>)null));"
               "        Case(\"null ints\", () => T0.P.LenOf((IReadOnlyList<int>)null));"
               "        Case(\"ints\", () => T0.P.LenOf(new int[] { 1, 2, 3 }));"
               "        Case(\"longs\", () => T0.P.LenOf(new List<long> { 1L, 2L }));"
               "        Case(\"nested ints\", () => T0.P.NestedInts(new (int, IReadOnlyList<int>)[] { (1, new int[] { 2, 3 }), (4, new int[0]) }));"
               "        Case(\"sorted ints\", () => T0.P.Search(new int[] { 1, 3, 5 }, 3));"
               "        Case(\"quantified left\", () => T0.P.SortedOnly(" + arr [ 2; 1 ] + "));"
               "        Case(\"quantified checked\", () => T2.P.SortedOnly(" + arr [ 2; 1 ] + "));"
               "        Case(\"same content\", () => T0.P.EqSeq(" + arr [ 1; 2 ] + ", " + arr [ 1; 2 ] + "));"
               "        Case(\"other content\", () => T0.P.EqSeq(" + arr [ 1; 2 ] + ", " + arr [ 1; 3 ] + "));"
               "        Case(\"unproved\", () => T1.P.Wrong(" + big 1 + "));"
               "        Case(\"bounds\", () => T1.P.OutOfBounds(" + arr [ 1 ] + "));" ])

[<Theory>]
[<InlineData("keywords", "5")>]
[<InlineData("scopes", "2")>]
[<InlineData("lambda then let", "7")>]
[<InlineData("empty tuples", "[]")>]
[<InlineData("nested empty", "[[], [1]]")>]
[<InlineData("empty arg", "0")>]
[<InlineData("huge", "123456789012345678901234567890")>]
[<InlineData("deep", "!InsufficientExecutionStackException")>]
[<InlineData("requires", "!ArgumentException")>]
[<InlineData("null", "!ArgumentNullException")>]
[<InlineData("null ints", "!ArgumentNullException")>]
[<InlineData("ints", "3")>]
[<InlineData("longs", "2")>]
[<InlineData("nested ints", "[(1, [2, 3]), (4, []), (1, [2, 3])]")>]
[<InlineData("sorted ints", "1")>]
[<InlineData("quantified left", "2")>]
[<InlineData("quantified checked", "!ArgumentException")>]
[<InlineData("same content", "true")>]
[<InlineData("other content", "false")>]
[<InlineData("unproved", "!QuodContractException")>]
[<InlineData("bounds", "!ArgumentOutOfRangeException")>]
let ``what differs from Python`` (label: string, expected: string) =
    // an array raises IndexOutOfRangeException where a List raises ArgumentOutOfRangeException
    let got = traps.Value.[label]
    if label = "bounds" then Assert.Contains("OutOfRange", got) else Assert.Equal(expected, got)

[<Fact>]
let ``the calling project can turn on the quantified requires with a symbol`` () =
    let src = "fn sorted_only(xs: seq<int>) -> int requires forall i in 0..len(xs) - 1: xs[i] <= xs[i + 1] { len(xs) }"
    let got =
        buildAndRunWith "QUOD_CHECK_REQUIRES" "net10.0" [ generated 0 src Set.empty false ]
            [ "        Case(\"bad\", () => T0.P.SortedOnly(new int[] { 2, 1 }));"
              "        Case(\"good\", () => T0.P.SortedOnly(new int[] { 1, 2 }));" ]
    Assert.Equal("!ArgumentException", got.["bad"])
    Assert.Equal("2", got.["good"])

[<Fact>]
let ``constants are named, not rebuilt at each use`` () =
    match generate "p.quod" (typedOf "fn f(x: int) -> int ensures result == x + 2 { x + 2 }") Set.empty defaultOptions with
    | Ok code ->
        Assert.Contains("private static readonly BigInteger _quod_2", code)
        Assert.Contains("(x + _quod_2)", code)
    | Result.Error why -> failwith why

[<Fact>]
let ``two functions with the same public name are refused`` () =
    match generate "p.quod" (typedOf "fn foo_bar() -> int { 1 } fn fooBar() -> int { 2 }") Set.empty defaultOptions with
    | Result.Error why -> Assert.Contains("FooBar", why)
    | Ok _ -> failwith "generated"

[<Fact>]
let ``a function named like its file does not name the class`` () =
    match generate "rotate.quod" (typedOf "fn rotate() -> int { 1 }") Set.empty defaultOptions with
    | Ok code ->
        Assert.Contains("class RotateModule", code)
        Assert.Contains("public static BigInteger Rotate()", code)
    | Result.Error why -> failwith why

[<Fact>]
let ``a namespace that is not one is refused`` () =
    match generate "p.quod" (typedOf "fn f() -> int { 1 }") Set.empty { defaultOptions with Namespace = "a b" } with
    | Result.Error why -> Assert.Contains("namespace", why)
    | Ok _ -> failwith "generated"

[<Fact>]
let ``the comment of a public method says which requires it leaves to the caller`` () =
    let src = "fn f(xs: seq<int>, n: int) -> int requires n > 0 requires forall i in 0..len(xs): xs[i] > 0 ensures result == n { n }"
    match generate "p.quod" (typedOf src) Set.empty defaultOptions with
    | Ok code ->
        Assert.Contains("requires n &gt; 0 (checked)", code)
        Assert.Contains("NOT CHECKED, the caller's duty, unless QUOD_CHECK_REQUIRES is defined: requires forall", code)
    | Result.Error why -> failwith why
