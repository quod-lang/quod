module Quod.Tests.CodegenTests

open System
open System.Diagnostics
open System.IO
open System.Numerics
open Xunit
open Quod.Typed
open Quod.Eval
open Quod.Tests.VerifyTests

/// python for the tests: `python`, then `python3`, on PATH.
let pythonPath =
    let works (exe: string) =
        try
            use p = Process.Start(ProcessStartInfo(exe, "--version", RedirectStandardOutput = true, UseShellExecute = false))
            p.WaitForExit()
            p.ExitCode = 0
        with _ -> false
    match [ "python"; "python3" ] |> List.tryFind works with
    | Some p -> p
    | None -> failwith "python not found on PATH: needed to run the generated code"

/// Type-check and verify (everything must pass), then generate Python.
let compile (src: string) : TProgram * string =
    let prog = Quod.Parser.parseProgram "test.quod" src
    let typed, errs = Quod.Typecheck.check "test.quod" prog
    Assert.True(errs.IsEmpty, "type errors: " + String.concat " | " (errs |> List.map (fun d -> d.Message)))
    let ds = verifyAll src |> List.filter (fun d -> d.Severity = Quod.Diagnostics.Error)
    Assert.True(ds.IsEmpty, "verification failed: " + String.concat " | " (ds |> List.map Quod.Diagnostics.toText))
    typed, Quod.CodegenPython.generate "test.quod" typed Set.empty

/// Run `driver` after the generated module (in one file, in a fresh directory); returns stdout.
let runPythonWith (flags: string) (modul: string) (driver: string) : string =
    let dir = Directory.CreateTempSubdirectory("quod-py-").FullName
    try
        let file = Path.Combine(dir, "test_quod.py")
        File.WriteAllText(file, modul + "\n\n" + driver)
        let psi = ProcessStartInfo(pythonPath, flags + " -I \"" + file + "\"", RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false)
        use p = Process.Start psi
        let out = p.StandardOutput.ReadToEndAsync()
        let err = p.StandardError.ReadToEnd()
        p.WaitForExit()
        Assert.True((p.ExitCode = 0), "python failed: " + err)
        out.Result.Replace("\r\n", "\n")
    finally
        Directory.Delete(dir, true)

let runPython = runPythonWith ""

let rec pyLiteral (v: Value) =
    match v with
    | VInt n -> n.ToString()
    | VBool b -> if b then "True" else "False"
    | VSeq xs -> "[" + (xs |> List.map pyLiteral |> String.concat ", ") + "]"
    | VTuple [ x ] -> "(" + pyLiteral x + ",)"
    | VTuple xs -> "(" + (xs |> List.map pyLiteral |> String.concat ", ") + ")"

/// Python code printing a value as Quod's valueText does.
let private quodText =
    "def _show(v):\n"
    + "    if isinstance(v, bool): return 'true' if v else 'false'\n"
    + "    if isinstance(v, int): return str(v)\n"
    + "    if isinstance(v, list): return '[' + ', '.join(_show(x) for x in v) + ']'\n"
    + "    return '(' + ', '.join(_show(x) for x in v) + ')'\n"

/// Read back a value printed by _show, at the type the function returns.
let parseValue (t: Ty) (text: string) : Value =
    let mutable pos = 0
    let peek () = if pos < text.Length then text.[pos] else '\000'
    let skip () = while peek () = ' ' || peek () = ',' do pos <- pos + 1
    let rec value (t: Ty) : Value =
        skip ()
        match t with
        | TyBool ->
            if text.Substring(pos).StartsWith "true" then (pos <- pos + 4; VBool true) else (pos <- pos + 5; VBool false)
        | TySeq e ->
            pos <- pos + 1
            let items = ResizeArray()
            skip ()
            while peek () <> ']' do
                items.Add(value e)
                skip ()
            pos <- pos + 1
            VSeq(List.ofSeq items)
        | TyTuple ts ->
            pos <- pos + 1
            let items = ts |> List.map value
            skip ()
            pos <- pos + 1
            VTuple items
        | _ ->
            let start = pos
            if peek () = '-' then pos <- pos + 1
            while Char.IsDigit(peek ()) do pos <- pos + 1
            VInt(BigInteger.Parse(text.Substring(start, pos - start)))
    value t

/// Small random values of a type (ints in -6..6, sequences of length 0..5).
let rec randomValue (rnd: Random) (t: Ty) : Value =
    match t with
    | TyInt | TyError -> VInt(BigInteger(rnd.Next(-6, 7)))
    | TyNat -> VInt(BigInteger(rnd.Next(0, 7)))
    | TyBool -> VBool(rnd.Next 2 = 0)
    | TySeq e -> VSeq [ for _ in 1 .. rnd.Next(0, 6) -> randomValue rnd e ]
    | TyTuple ts -> VTuple(ts |> List.map (randomValue rnd))

/// Run every function of `src` in Python on random inputs that satisfy its precondition.
/// An expression function must give what the evaluator gives; a statement function (which
/// the evaluator cannot run) must satisfy its proved ensures clauses. Returns the cases run.
let differential (src: string) (casesPerFn: int) : int =
    let typed, modul = compile src
    let ev = Evaluator(typed.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList)
    let rnd = Random 20261022
    let cases = ResizeArray<TFn * Map<string, Value>>()
    for f in typed.Fns do
        let mutable found, tries = 0, 0
        while found < casesPerFn && tries < 20000 do
            tries <- tries + 1
            let env = f.Params |> List.map (fun p -> p.Name, randomValue rnd p.Ty) |> Map.ofList
            if f.Requires |> List.forall (fun r -> ev.Holds(r, env) = Some true) then
                found <- found + 1
                cases.Add((f, env))
        Assert.True(found > 0, "no input satisfies the precondition of " + f.Name)
    let calls =
        cases
        |> Seq.map (fun (f, env) ->
            let args = f.Params |> List.map (fun p -> pyLiteral env.[p.Name]) |> String.concat ", "
            "print(_show(" + Quod.CodegenPython.pyName f.Name + "(" + args + ")))")
        |> String.concat "\n"
    let lines = (runPython modul (quodText + calls)).TrimEnd('\n').Split('\n')
    Assert.Equal(cases.Count, lines.Length)
    for (f, env), line in Seq.zip cases lines do
        let got = parseValue f.Ret line
        let show () = f.Name + "(" + (f.Params |> List.map (fun p -> valueText env.[p.Name]) |> String.concat ", ") + ") = " + line
        match f.Body with
        | TExprBody body -> Assert.True((ev.Expr(body, env) = got), show () + ", the evaluator gives " + valueText (ev.Expr(body, env)))
        | TStmtBody _ ->
            Assert.True(ev.Fits(f.Ret, got), show () + " is not a " + tyText f.Ret)
            for e in f.Ensures do
                Assert.True((ev.Holds(e, env.Add("result", got)) = Some true), show () + " violates an ensures clause")
    cases.Count

let private repoFile (relative: string) =
    let rec up (d: DirectoryInfo) =
        if File.Exists(Path.Combine(d.FullName, relative)) then Path.Combine(d.FullName, relative) else up d.Parent
    up (DirectoryInfo AppContext.BaseDirectory)

[<Fact>]
let ``the example runs in Python as the evaluator and the contracts say`` () =
    let n = differential (File.ReadAllText(repoFile "examples/binary_search.quod")) 150
    Assert.True(n >= 300)

[<Fact>]
let ``arithmetic, sequences, tuples and quantifiers agree with the evaluator`` () =
    let src =
        "fn ediv(a: int, b: int) -> (int, int) requires b != 0 { (a / b, a % b) }\n"
        + "fn neg_mod(a: int) -> int { a % -3 }\n"
        + "fn mix(xs: seq<int>, k: nat) -> seq<int> requires k <= len(xs) { xs[k..] + xs[..k] + [len(xs) - k] }\n"
        + "fn logic(a: bool, b: bool) -> bool { (a ==> b) <==> (!a || b) && !(a && !b) }\n"
        + "fn pick(p: (int, (bool, seq<int>))) -> seq<int> { if p.1.0 { p.1.1 + [p.0] } else { [] } }\n"
        + "fn chain(a: int, b: int, c: int) -> bool { a <= b < c }\n"
        + "fn neg(x: int) -> int { -x - -1 }\n"
    differential src 120 |> ignore

[<Fact>]
let ``statement functions satisfy their proved contracts at run time`` () =
    let src =
        "fn sum_to(n: nat) -> int ensures result == n * (n + 1) / 2 {\n"
        + "  let mut i = 0; let mut s = 0;\n"
        + "  while i < n invariant 0 <= i <= n invariant s == i * (i + 1) / 2 decreases n - i { i = i + 1; s = s + i; }\n"
        + "  return s; }\n"
        + "fn index_of_max(xs: seq<int>) -> nat requires len(xs) > 0 ensures result < len(xs) ensures forall j in 0..len(xs): xs[j] <= xs[result] loose (r1, r2) => xs[r1] == xs[r2] {\n"
        + "  let mut best = 0; let mut i = 1;\n"
        + "  while i < len(xs) invariant 1 <= i <= len(xs) invariant 0 <= best < len(xs) invariant forall j in 0..i: xs[j] <= xs[best] decreases len(xs) - i\n"
        + "  { if xs[i] > xs[best] { best = i; } i = i + 1; }\n"
        + "  return best; }\n"
    differential src 100 |> ignore

[<Fact>]
let ``Quod names that are Python keywords or builtins are renamed or protected`` () =
    let src =
        "fn len2(lambda: seq<int>, pass: int) -> int { len(lambda) + pass }\n"
        + "fn list(range: int) -> seq<int> { [range] }\n"
        + "fn all(x: int) -> bool { x == 0 }\n"
    let _, modul = compile src
    Assert.Contains("def len2(lambda_: list[int], pass_: int) -> int:", modul)
    let out = runPython modul "print(len2([1, 2], 3), list(4), all(0), all(1))"
    Assert.Equal("5 [4] True False\n", out)

[<Fact>]
let ``callers cannot alias a sequence argument, and tuples are accepted for sequences`` () =
    let _, modul = compile "fn grow(xs: seq<int>) -> seq<int> { xs + [0] }"
    let out = runPython modul "a = [1]\nb = grow(a)\nb.append(9)\nprint(a, b, grow((5, 6)))"
    Assert.Equal("[1] [1, 0, 9] [5, 6, 0]\n", out)

[<Fact>]
let ``proved contracts produce no checks; unproved ones are checked with --runtime-checks`` () =
    let src = "fn dec(x: int) -> int ensures result > x { x - 1 }"
    let prog = Quod.Parser.parseProgram "test.quod" src
    let typed, _ = Quod.Typecheck.check "test.quod" prog
    let checkedCode = Quod.CodegenPython.generate "test.quod" typed (Set.singleton "dec")
    Assert.Contains("WARNING: not fully proved", checkedCode)
    let out = runPython checkedCode "try:\n    dec(3)\n    print('no error')\nexcept AssertionError as e:\n    print('caught:', e)"
    Assert.Equal("caught: postcondition not proved: checked at run time\n", out)
    let _, provedCode = compile "fn inc(x: int) -> int ensures result == x + 1 { x + 1 }"
    Assert.DoesNotContain("AssertionError", provedCode)

[<Fact>]
let ``quantified contracts checked at run time use Python's all and any`` () =
    let src =
        "fn top(xs: seq<int>) -> int requires exists i in 0..len(xs): xs[i] > 0 ensures forall i in 0..len(xs): xs[i] <= result { xs[0] }"
    let prog = Quod.Parser.parseProgram "test.quod" src
    let typed, _ = Quod.Typecheck.check "test.quod" prog
    let code = Quod.CodegenPython.generate "test.quod" typed (Set.singleton "top")
    let driver =
        "for xs in ([3, -1], [-2, 5], [-1, -2]):\n"
        + "    try:\n        print(top(xs))\n"
        + "    except AssertionError as e:\n        print(e)"
    Assert.Equal("3\npostcondition not proved: checked at run time\nprecondition not proved: checked at run time\n", runPython code driver)
[<Fact>]
let ``run-time checks survive python -O, and invariants are checked after the last iteration`` () =
    let src =
        "fn sum_to(n: nat) -> int ensures result == n * (n + 1) / 2 {\n"
        + "  let mut i = 0; let mut s = 0;\n"
        + "  while i < n invariant 0 <= i <= n invariant s == i * (i + 1) / 2 decreases n - i { i = i + 1; s = s + 1; }\n"
        + "  return s; }\n"
    let prog = Quod.Parser.parseProgram "test.quod" src
    let typed, _ = Quod.Typecheck.check "test.quod" prog
    let code = Quod.CodegenPython.generate "test.quod" typed (Set.singleton "sum_to")
    let driver = "for n in (1, 2):\n    try:\n        print(sum_to(n))\n    except AssertionError as e:\n        print(e)"
    Assert.Equal("1\ninvariant not proved: checked at run time\n", runPythonWith "-O" code driver)
[<Fact>]
let ``unproved bounds are checked at run time, where Python would wrap or clamp`` () =
    let src = "fn last(xs: seq<int>) -> int { xs[len(xs) - 1] }\nfn tail(xs: seq<int>, k: int) -> seq<int> { xs[k..] }"
    let prog = Quod.Parser.parseProgram "test.quod" src
    let typed, _ = Quod.Typecheck.check "test.quod" prog
    let code = Quod.CodegenPython.generate "test.quod" typed (set [ "last"; "tail" ])
    let driver =
        "for f, a in ((last, ([4, 5],)), (last, ([],)), (tail, ([1, 2], 1)), (tail, ([1, 2], -1)), (tail, ([1, 2], 3))):\n"
        + "    try:\n        print(f(*a))\n"
        + "    except IndexError as e:\n        print(e)"
    Assert.Equal(
        "5\nindex -1 out of bounds (not proved: checked at run time)\n[2]\n"
        + "slice -1..2 out of bounds (not proved: checked at run time)\nslice 3..2 out of bounds (not proved: checked at run time)\n",
        runPython code driver)