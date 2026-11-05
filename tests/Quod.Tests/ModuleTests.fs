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

// --- i32 and i64 ------------------------------------------------------------------------------------

let private proofError (src: string) (expected: string) =
    withFiles [ "main", src ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) ->
            Assert.Contains(errorsOf r, fun d -> d.Kind = "proof" && d.Message.Contains expected && not d.Counterexample.IsEmpty)
        | other -> failwithf "%A" other)

let private proved (src: string) =
    withFiles [ "main", src ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.Empty(errorsOf r)
        | other -> failwithf "%A" other)

[<Fact>]
let ``an operation that can leave the bounds is refused, with a counterexample`` () =
    proofError "fn add(a: i32, b: i32) -> i32\n  ensures result == a + b\n{\n  a + b\n}\n" "fits in i32"
    proofError "fn neg(a: i32) -> i32\n  ensures result == -a\n{\n  -a\n}\n" "fits in i32"
    proofError "fn mul(a: i64, b: i64) -> i64\n  ensures result == a * b\n{\n  a * b\n}\n" "fits in i64"
    proofError "fn narrow(x: int) -> i32\n  ensures result == x\n{\n  to_i32(x)\n}\n" "fits in i32"

[<Fact>]
let ``arithmetic is mathematical in a contract`` () =
    proved "fn add(a: i32, b: i32) -> i64\n  ensures result == a + b\n{\n  let x: i64 = a;\n  x + b\n}\n"

[<Fact>]
let ``nothing narrows by itself, and a literal must fit`` () =
    typeError "fn f(x: int) -> i32 {\n  x\n}\n" "to_i32"
    typeError "fn f(x: i64) -> i32 {\n  x\n}\n" "to_i32"
    typeError "fn f() -> i32 {\n  3000000000\n}\n" "does not fit in i32"

[<Fact>]
let ``a sequence does not convert`` () =
    typeError "fn f(xs: seq<i32>) -> seq<int> {\n  xs\n}\n" "seq<int> is expected"
    typeError "fn f(xs: seq<i32>, ys: seq<int>) -> bool {\n  xs == ys\n}\n" "different types"

[<Fact>]
let ``a length converts, in a program with bounded integers`` () =
    proved "fn last(xs: seq<i32>) -> i32\n  requires len(xs) >= 1\n  ensures result == xs[len(xs) - 1]\n{\n  xs[to_i32(len(xs)) - 1]\n}\n"

[<Fact>]
let ``i32 and i64 remain possible names of variables`` () =
    proved "fn f(i32: int, i64: int) -> int\n  ensures result == i32 + i64\n{\n  i32 + i64\n}\n"

// --- struct, enum, match and generics -----------------------------------------------------------------

let private color = "enum Color { Red, Green, Rgb(int, int, int) }\n\n"

[<Fact>]
let ``a match covers every case`` () =
    typeError (color + "fn f(c: Color) -> int {\n  match c { Red => 1, Green => 2 }\n}\n") "forgets the case(s) 'Rgb'"
    typeError (color + "fn f(c: Color) -> int {\n  match c { Red => 1, Red => 2, _ => 3 }\n}\n") "appears twice"
    typeError (color + "fn f(c: Color) -> int {\n  match c { Blue => 1, _ => 3 }\n}\n") "no case 'Blue'"
    typeError (color + "fn f(c: Color) -> int {\n  match c { Rgb(a) => a, _ => 3 }\n}\n") "3 field(s), 1 named"
    typeError (color + "fn f(c: Color) -> int {\n  match c { _ => 3, Red => 1 }\n}\n") "'_' comes last"
    typeError "fn f(x: int) -> int {\n  match x { _ => 3 }\n}\n" "needs an enum"

[<Fact>]
let ``a type cannot hold itself`` () =
    typeError "enum L { Nil, Cons(int, L) }\n\nfn f() -> int {\n  1\n}\n" "holds itself"
    typeError "enum L<T> { Nil, Cons(T, L<T>) }\n\nfn f(x: L<int>) -> int {\n  1\n}\n" "holds itself"

[<Fact>]
let ``fields and names are checked`` () =
    typeError "struct P { x: int }\n\nfn f(p: P) -> int {\n  p.y\n}\n" "no field 'y'"
    typeError "struct P { x: int }\n\nfn f() -> P {\n  P(1, 2)\n}\n" "takes 1 value(s)"
    typeError "struct P { x: nat }\n\nfn f() -> P {\n  P(true)\n}\n" "the field 'x'"
    typeError (color + "enum Other { Red }\n\nfn f() -> int {\n  1\n}\n") "already the name"
    typeError (color + "fn f(c: Color) -> int {\n  c.x\n}\n") "read with 'match'"

[<Fact>]
let ``a proof goes through each case, and a counterexample names one`` () =
    proved (color + "fn f(c: Color) -> int\n  ensures match c { Rgb(a, _, _) => result == a, _ => result == 0 }\n{\n  match c { Rgb(a, _, _) => a, _ => 0 }\n}\n")
    proofError (color + "fn f(c: Color) -> int\n  ensures result > 1\n{\n  match c { Red => 1, _ => 3 }\n}\n") "postcondition"

[<Fact>]
let ``a field keeps what its type promises`` () =
    proved "struct P { n: nat, s: i32 }\n\nfn f(p: P) -> bool\n  ensures result == true\n{\n  p.n >= 0 && p.s <= 2147483647\n}\n"

[<Fact>]
let ``completeness speaks of data`` () =
    withFiles [ "main", color + "fn f(x: int) -> Color\n  ensures x > 0 ==> result == Red\n{\n  if x > 0 { Red } else { Green }\n}\n" ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.Contains(errorsOf r, fun d -> d.Kind = "completeness" && not d.Counterexample.IsEmpty)
        | other -> failwithf "%A" other)

[<Fact>]
let ``enum, struct and match remain possible names`` () =
    proved "fn f(enum: int, struct: int, match: int) -> int\n  ensures result == enum + struct + match\n{\n  enum + struct + match\n}\n"

[<Fact>]
let ``a generic is copied for its types, and proved for each`` () =
    proved "import option\n\nfn first<T>(xs: seq<T>) -> option.Option<T>\n  ensures len(xs) > 0 ==> result == option.Some(xs[0])\n  ensures len(xs) == 0 ==> result == option.None\n{\n  if len(xs) == 0 { option.None } else { option.Some(xs[0]) }\n}\n\nfn a(xs: seq<int>) -> option.Option<int>\n  ensures result == first(xs)\n{\n  first(xs)\n}\n\nfn b(xs: seq<string>) -> option.Option<string>\n  ensures result == first(xs)\n{\n  first(xs)\n}\n"
    withFiles [ "main", "fn id<T>(x: T) -> T\n  ensures result == x\n{\n  x\n}\n\nfn a(n: int) -> int\n  ensures result == n\n{\n  id(n)\n}\n" ] (fun _ outcome ->
        match outcome with
        | Checked(typed, _) -> Assert.Contains(typed.Fns, fun f -> f.Name = "id__int")
        | other -> failwithf "%A" other)

[<Fact>]
let ``nothing says what the type parameter is`` () =
    typeError "import option\n\nfn f() -> int {\n  let x = option.None;\n  1\n}\n" "nothing here says"

[<Fact>]
let ``types go across modules`` () =
    withFiles
        [ "lib", "struct P { x: int }\n\nenum E { A, B(P) }\n\nfn mk(n: int) -> E\n  ensures result == B(P(n))\n{\n  B(P(n))\n}\n"
          "main", "import lib\n\nfn f(n: int) -> int\n  ensures result == n\n{\n  match lib.mk(n) { A => 0, B(p) => p.x }\n}\n\nfn g() -> lib.E\n  ensures result == lib.A\n{\n  lib.A\n}\n" ]
        (fun _ outcome ->
            match outcome with
            | Checked(_, r) -> Assert.Empty(errorsOf r)
            | other -> failwithf "%A" other)

[<Fact>]
let ``a tail call does not grow the stack`` () =
    let src = "import strings\n\nfn t(s: string) -> string\n  ensures result == strings.trim(s)\n{\n  strings.trim(s)\n}\n\nfn n(s: string, c: char) -> nat\n  ensures result == len(strings.split(s, c))\n{\n  len(strings.split(s, c))\n}\n\nfn d(s: string) -> bool\n  ensures result == strings.all_digits(s)\n{\n  strings.all_digits(s)\n}\n\nfn j(xs: seq<string>) -> nat\n  ensures result == len(strings.join(xs, \",\"))\n{\n  len(strings.join(xs, \",\"))\n}\n"
    withFiles [ "main", src ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            Assert.Empty(errorsOf r)
            match generate (Python false) (Path.Combine(dir, "main.quod")) typed r false with
            | Result.Error why -> failwith why
            | Ok g ->
                File.WriteAllText(Path.Combine(dir, "main.py"), g.Code)
                for m, text in g.Imported do File.WriteAllText(Path.Combine(dir, m + ".py"), text)
                let psi = Diagnostics.ProcessStartInfo("python", "-c \"import main; print(len(main.t(' ' * 50000 + 'a' + ' ' * 50000))); print(main.n(','.join(['x'] * 5000), ',')); print(main.d('1' * 50000)); print(main.j(['x'] * 5000))\"")
                psi.WorkingDirectory <- dir
                psi.RedirectStandardOutput <- true
                psi.UseShellExecute <- false
                use p = Diagnostics.Process.Start psi
                let out = p.StandardOutput.ReadToEnd().Replace("\r\n", "\n").Trim()
                p.WaitForExit()
                Assert.Equal("1\n5000\nTrue\n9999", out)
        | other -> failwithf "%A" other)

[<Fact>]
let ``the fields of a case can have names`` () =
    proved "enum D { Accepted(value: int, why: string), No }\n\nfn f(d: D) -> int\n  ensures result == match d { Accepted(v, _) => v, No => 0 }\n{\n  match d { Accepted(v, _) => v, No => 0 }\n}\n"

[<Fact>]
let ``run_by needs a proof of equality`` () =
    typeError "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n" "no such function"
    typeError "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n\nfn g(y: int) -> int\n  ensures result == f(y)\n{\n  y\n}\n" "same parameters"
    typeError "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n\nfn g(x: int) -> int\n  ensures result == x\n{\n  x\n}\n" "must state"
    proved "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n\nfn g(x: int) -> int\n  ensures result == f(x)\n{\n  x\n}\n"

[<Fact>]
let ``a class keeps a copy of the lists it is given`` () =
    withFiles [ "main", "struct Batch { scores: seq<i32> }\n\nfn wrap(xs: seq<i32>) -> Batch\n  ensures result == Batch(xs)\n{\n  Batch(xs)\n}\n" ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (CSharp { Namespace = "N"; CheckAllRequires = false }) (Path.Combine(dir, "main.quod")) typed r false with
            | Ok g ->
                Assert.Contains(": this(_quod_copy(scores), true)", g.Code)
                Assert.Contains("return _quod_f_wrap(_quod_copy(xs));", g.Code)
            | Result.Error why -> failwith why
        | other -> failwithf "%A" other)

