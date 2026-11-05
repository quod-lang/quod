module Quod.Tests.ModuleTests

open System
open System.IO
open Xunit
open Quod.Diagnostics
open Quod.Pipeline
open Quod.Tests.VerifyTests

let private settings = { defaultSettings with Z3 = Some z3Path }

/// Check `main.quod` among these files, in a directory of their own.
let private withFiles (files: (string * string) list) (use': string -> Outcome -> unit) =
    let dir = Path.Combine(Path.GetTempPath(), "quod-modules-" + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory dir |> ignore
    try
        for name, text in files do File.WriteAllText(Path.Combine(dir, name + ".quod"), text)
        let main = Path.Combine(dir, "main.quod")
        use' dir (check main (File.ReadAllText main) settings)
    finally
        Directory.Delete(dir, true)

let private rejectedWith (expected: string) (fileOf: string) (files: (string * string) list) =
    withFiles files (fun _ outcome ->
        match outcome with
        | Rejected ds ->
            let d = ds |> List.tryFind (fun d -> d.Message.Contains expected)
            Assert.True(d.IsSome, "no error with '" + expected + "' in: " + String.Join(" | ", ds |> List.map (fun d -> d.Message)))
            Assert.Equal(fileOf, Path.GetFileName d.Value.File)
        | other -> failwithf "expected a rejection, got %A" other)

let private lib = "private fn twice(x: int) -> int {\n  x + x\n}\n\nfn quad(x: int) -> int\n  ensures result == twice(twice(x))\n{\n  twice(twice(x))\n}\n"

[<Fact>]
let ``an import that does not exist is an error of the importing file`` () =
    rejectedWith "no module 'absent'" "main.quod" [ "main", "import absent\n\nfn f() -> int {\n  1\n}\n" ]

[<Fact>]
let ``a cycle of imports is named`` () =
    rejectedWith "import cycle: main -> a -> main" "a.quod"
        [ "main", "import a\n\nfn f() -> int {\n  a.g()\n}\n"
          "a", "import main\n\nfn g() -> int {\n  1\n}\n" ]

[<Fact>]
let ``a private function is not called from another module`` () =
    rejectedWith "'twice' is private to module 'lib'" "main.quod"
        [ "lib", lib; "main", "import lib\n\nfn f(x: int) -> int {\n  lib.twice(x)\n}\n" ]

[<Fact>]
let ``a function of another module needs its full name`` () =
    rejectedWith "'lib.quad'" "main.quod"
        [ "lib", lib; "main", "import lib\n\nfn f(x: int) -> int {\n  quad(x)\n}\n" ]

[<Fact>]
let ``a module must be imported to be called`` () =
    rejectedWith "add 'import lib'" "main.quod"
        [ "lib", lib; "main", "fn f(x: int) -> int {\n  lib.quad(x)\n}\n" ]

[<Fact>]
let ``a module does not see the short names of the file that imports it`` () =
    rejectedWith "unknown function 'helper'" "lib.quod"
        [ "lib", "fn g(x: int) -> int {\n  helper(x)\n}\n"
          "main", "import lib\n\nfn helper(x: int) -> int {\n  x\n}\n\nfn f(x: int) -> int {\n  lib.g(helper(x))\n}\n" ]

[<Fact>]
let ``a syntax error of an imported module is reported in its file`` () =
    rejectedWith "" "lib.quod" [ "lib", "fn g( -> int {\n}\n"; "main", "import lib\n\nfn f() -> int {\n  1\n}\n" ]

[<Fact>]
let ``an import goes at the top`` () =
    rejectedWith "at the top of the file" "main.quod" [ "main", "fn f() -> int {\n  1\n}\n\nimport lib\n"; "lib", lib ]

[<Fact>]
let ``import and private remain possible names of variables`` () =
    withFiles [ "main", "fn f(import: int, private: int) -> int\n  ensures result == import + private\n{\n  import + private\n}\n" ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.Empty(errorsOf r)
        | other -> failwithf "%A" other)

[<Fact>]
let ``an expression function of a module is unfolded in the proofs of another`` () =
    withFiles
        [ "lib", lib
          "main", "import lib\n\nfn f(x: int) -> int\n  ensures result == 4 * x\n{\n  lib.quad(x)\n}\n" ]
        (fun _ outcome ->
            match outcome with
            | Checked(_, r) -> Assert.Empty(errorsOf r)
            | other -> failwithf "%A" other)

[<Fact>]
let ``a statement function of a module is known by its contract only`` () =
    let weak = "fn pos(x: int) -> int\n  ensures result >= 0\n{\n  let y = 7;\n  if x > y { x } else { y }\n}\n"
    withFiles
        [ "lib", weak
          "main", "import lib\n\nfn f(x: int) -> int\n  ensures result >= 7\n{\n  lib.pos(x)\n}\n" ]
        (fun _ outcome ->
            match outcome with
            | Checked(_, r) -> Assert.Contains(errorsOf r, fun d -> d.Kind = "proof" && d.Fn = Some "f")
            | other -> failwithf "%A" other)

[<Fact>]
let ``a failed proof in an imported module refuses the program, in that file`` () =
    withFiles
        [ "lib", "fn g(x: int) -> int\n  ensures result > x\n{\n  x\n}\n"
          "main", "import lib\n\nfn f(x: int) -> int\n  ensures result > x\n{\n  lib.g(x)\n}\n" ]
        (fun _ outcome ->
            match outcome with
            | Checked(_, r) ->
                let d = errorsOf r |> List.find (fun d -> d.Kind = "proof")
                Assert.Equal(Some "lib.g", d.Fn)
                Assert.Equal("lib.quod", Path.GetFileName d.File)
            | other -> failwithf "%A" other)

let private generated (target: Target) =
    let mutable out = None
    withFiles
        [ "lib", lib
          "main", "import lib\n\nfn f(x: int) -> int\n  ensures result == 4 * x\n{\n  lib.quad(x)\n}\n" ]
        (fun dir outcome ->
            match outcome with
            | Checked(typed, r) ->
                match generate target (Path.Combine(dir, "main.quod")) typed r false with
                | Ok g -> out <- Some g
                | Result.Error why -> failwith why
            | other -> failwithf "%A" other)
    out.Value

[<Fact>]
let ``python: a module per file, a private function has no public name`` () =
    let g = generated (Python false)
    Assert.Contains("import lib as _quod_m_lib", g.Code)
    Assert.Contains("_quod_m_lib.quad(", g.Code)
    let text = g.Imported |> List.find (fun (m, _) -> m = "lib") |> snd
    Assert.Contains("def quad(", text)
    Assert.Contains("_quod_f_twice(", text)
    Assert.DoesNotContain("def twice(", text)
    Assert.DoesNotContain("\"twice\"", text)

[<Fact>]
let ``csharp: a class per module, a private function has no public method`` () =
    let g = generated (CSharp { Namespace = "N"; CheckAllRequires = false })
    Assert.Contains("Lib.Quad(", g.Code)
    let text = g.Imported |> List.find (fun (m, _) -> m = "lib") |> snd
    Assert.Contains("public static class Lib", text)
    Assert.Contains("public static BigInteger Quad(", text)
    Assert.DoesNotContain("public static BigInteger Twice(", text)

[<Fact>]
let ``the generated modules run, in python`` () =
    let g = generated (Python false)
    let dir = Path.Combine(Path.GetTempPath(), "quod-modules-py-" + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory dir |> ignore
    try
        File.WriteAllText(Path.Combine(dir, "main.py"), g.Code)
        for m, text in g.Imported do File.WriteAllText(Path.Combine(dir, m + ".py"), text)
        let psi = Diagnostics.ProcessStartInfo("python", "-c \"import main; print(main.f(3))\"")
        psi.WorkingDirectory <- dir
        psi.RedirectStandardOutput <- true
        psi.UseShellExecute <- false
        use p = Diagnostics.Process.Start psi
        let out = p.StandardOutput.ReadToEnd().Trim()
        p.WaitForExit()
        Assert.Equal("12", out)
    finally
        Directory.Delete(dir, true)

// --- char, string and the standard library ---------------------------------------------------------

let private strProgram =
    "import strings\n\nfn parts(s: string) -> seq<string>\n  ensures result == strings.split(strings.trim(s), ',')\n{\n  strings.split(strings.trim(s), ',')\n}\n\n"
    + "fn again(s: string) -> string\n  ensures result == strings.join(parts(s), \"; \")\n{\n  strings.join(parts(s), \"; \")\n}\n\n"
    + "fn plus_one(s: string) -> string\n  requires strings.is_int(s)\n  ensures result == strings.int_to_string(strings.parse_int(s) + 1)\n{\n  strings.int_to_string(strings.parse_int(s) + 1)\n}\n"

[<Fact>]
let ``the standard library is found, proved with the program, and runs`` () =
    withFiles [ "main", strProgram ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            Assert.Empty(errorsOf r)
            match generate (Python false) (Path.Combine(dir, "main.quod")) typed r false with
            | Result.Error why -> failwith why
            | Ok g ->
                File.WriteAllText(Path.Combine(dir, "main.py"), g.Code)
                for m, text in g.Imported do File.WriteAllText(Path.Combine(dir, m + ".py"), text)
                let psi = Diagnostics.ProcessStartInfo("python", "-c \"import main; print(main.parts(' a,,b\\n')); print(main.again('x,y')); print(main.plus_one('-42')); print(main.plus_one('99'))\"")
                psi.WorkingDirectory <- dir
                psi.RedirectStandardOutput <- true
                psi.UseShellExecute <- false
                use p = Diagnostics.Process.Start psi
                let out = p.StandardOutput.ReadToEnd().Replace("\r\n", "\n").Trim()
                p.WaitForExit()
                Assert.Equal("['a', '', 'b']\nx; y\n-41\n100", out)
        | other -> failwithf "%A" other)

[<Fact>]
let ``a local file hides a module of the standard library, with a warning`` () =
    withFiles
        [ "strings", "fn id(x: int) -> int\n  ensures result == x\n{\n  x\n}\n"
          "main", "import strings\n\nfn f(x: int) -> int\n  ensures result == x\n{\n  strings.id(x)\n}\n" ]
        (fun _ outcome ->
            match outcome with
            | Checked(_, r) -> Assert.Contains(r.Diagnostics, fun d -> d.Status = "shadow" && d.Severity = Warning)
            | other -> failwithf "%A" other)

let private typeError (src: string) (expected: string) =
    rejectedWith expected "main.quod" [ "main", src ]

[<Fact>]
let ``a char is not an integer`` () =
    typeError "fn f(c: char) -> int {\n  c + 1\n}\n" "must be an int"
    typeError "fn f(x: int) -> char {\n  x\n}\n" "char"

[<Fact>]
let ``a literal holds one character, and an escape a scalar value`` () =
    rejectedWith "one character" "main.quod" [ "main", "fn f() -> char {\n  'ab'\n}\n" ]
    rejectedWith "scalar value" "main.quod" [ "main", "fn f() -> char {\n  '\\u{D800}'\n}\n" ]
    rejectedWith "not closed" "main.quod" [ "main", "fn f() -> string {\n  \"ab\n}\n" ]

[<Fact>]
let ``char_of has an obligation`` () =
    withFiles [ "main", "fn f(n: int) -> char {\n  char_of(n)\n}\n" ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.Contains(errorsOf r, fun d -> d.Kind = "proof")
        | other -> failwithf "%A" other)

[<Fact>]
let ``string and char remain possible names of variables`` () =
    withFiles [ "main", "fn f(string: int, char: int) -> int\n  ensures result == string + char\n{\n  string + char\n}\n" ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.Empty(errorsOf r)
        | other -> failwithf "%A" other)

