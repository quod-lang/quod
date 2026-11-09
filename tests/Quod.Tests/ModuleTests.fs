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
    Assert.Contains("public static long Quad(", text)
    Assert.DoesNotContain("public static long Twice(", text)

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
let ``a length converts, with a requires that says it fits`` () =
    proved "fn last(xs: seq<i32>) -> i32\n  requires len(xs) >= 1 && len(xs) <= 2147483647\n  ensures result == xs[len(xs) - 1]\n{\n  xs[to_i32(len(xs)) - 1]\n}\n"

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

// --- what the review of 0.3 found ----------------------------------------------------------------------

let private notVerified (src: string) =
    withFiles [ "main", src ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) -> Assert.NotEmpty(errorsOf r)
        | Rejected _ -> ()
        | other -> failwithf "%A" other)

[<Fact>]
let ``the length of a term that does not exist has no bound`` () =
    notVerified "fn wrong(xs: seq<bool>) -> bool\n  ensures !result\n{\n  let k: i32 = 0;\n  assert len(xs + xs) >= k;\n  len(xs) > 1073741823\n}\n"
    // through a lemma, a parameter or a string: nothing is assumed of a length any more
    notVerified "lemma fits(s: seq<bool>)\n  ensures len(s) <= 2147483647\n{\n}\n\nfn wrong(xs: seq<bool>) -> bool\n  ensures !result\n{\n  let k: i32 = 0;\n  fits(xs + xs);\n  len(xs) > 1073741824\n}\n"
    notVerified "fn wrong(s: string) -> bool\n  ensures !result\n{\n  let k: i32 = 0;\n  len(s) > 2147483647\n}\n"
    notVerified "fn f(xs: seq<i32>) -> i32\n  ensures result == len(xs)\n{\n  to_i32(len(xs))\n}\n"
    proved "fn f(xs: seq<i32>) -> i32\n  requires len(xs) <= 2147483647\n  ensures result == len(xs)\n{\n  to_i32(len(xs))\n}\n"

[<Fact>]
let ``run_by cannot require more, nor call back`` () =
    typeError "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n\nfn g(x: int) -> int\n  requires x == 1\n  ensures result == f(x)\n{\n  1\n}\n" "does not: it would run"
    typeError "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n\nfn g(x: int) -> int\n  ensures result == f(x)\n{\n  f(x)\n}\n" "would loop"
    proved "fn f(x: int) -> int\n  requires x > 0\n  run_by g\n{\n  x\n}\n\nfn g(x: int) -> int\n  requires x > 0\n  ensures result == f(x)\n{\n  x\n}\n"

[<Fact>]
let ``a contract cannot mention its own function`` () =
    typeError "fn f(x: int) -> int\n  ensures result == f(x)\n{\n  x + 1\n}\n" "mentions 'f'"

[<Fact>]
let ``a literal too large for a bounded integer makes the operation an int`` () =
    proved "fn f(x: i32) -> bool\n  ensures result == true\n{\n  x < 3000000000\n}\n"

[<Fact>]
let ``an unused generic is said to be unchecked, but not those of the library`` () =
    withFiles [ "main", "import option\n\nfn bad<T>(x: T) -> T {\n  x + 1\n}\n" ] (fun _ outcome ->
        match outcome with
        | Checked(_, r) ->
            let warned = r.Diagnostics |> List.filter (fun d -> d.Status = "unused-generic")
            Assert.Equal(1, warned.Length)
            Assert.Equal(Some "bad", warned.Head.Fn)
        | other -> failwithf "%A" other)

[<Fact>]
let ``C#: division by -1 is guarded, and a class is equal by value`` () =
    withFiles [ "main", "struct B { xs: seq<i32> }\n\nenum E { A, C(value: i32) }\n\nfn md(a: i32, b: i32) -> i32\n  requires b != 0\n  ensures result == a % b\n{\n  a % b\n}\n" ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (CSharp { Namespace = "N"; CheckAllRequires = false }) (Path.Combine(dir, "main.quod")) typed r false with
            | Ok g ->
                Assert.Contains("if (b == -1) return 0;", g.Code)
                Assert.Contains("IEquatable<B>", g.Code)
                Assert.Contains("operator ==(B a, B b)", g.Code)
                Assert.Contains("_quod_hash(_f0", g.Code)
                Assert.Contains("public R Match<R>(Func<R> onA, Func<int, R> onC)", g.Code)
                Assert.Contains("new _QuodView<int, int>(_f0", g.Code)
            | Result.Error why -> failwith why
        | other -> failwithf "%A" other)

// --- what the second review of 0.3 found ---------------------------------------------------------------

let private pythonOf (src: string) (run: string) (runtimeChecks: bool) : string =
    let mutable out = ""
    withFiles [ "main", src ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (Python false) (Path.Combine(dir, "main.quod")) typed r runtimeChecks with
            | Result.Error why -> failwith why
            | Ok g ->
                File.WriteAllText(Path.Combine(dir, "main.py"), g.Code)
                for m, text in g.Imported do File.WriteAllText(Path.Combine(dir, m + ".py"), text)
                let psi = Diagnostics.ProcessStartInfo("python", "-c \"" + run + "\"")
                psi.WorkingDirectory <- dir
                psi.RedirectStandardOutput <- true
                psi.RedirectStandardError <- true
                psi.UseShellExecute <- false
                use p = Diagnostics.Process.Start psi
                out <- p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd()
                p.WaitForExit()
        | other -> failwithf "%A" other)
    out.Replace("\r\n", "\n").Trim()

[<Fact>]
let ``two underscores are reserved, so a function cannot capture a copy`` () =
    rejectedWith "reserved for the compiler" "main.quod" [ "main", "fn id__int(x: int) -> int\n  ensures result == x + 1\n{\n  x + 1\n}\n" ]

[<Fact>]
let ``two copies of a generic never share a name`` () =
    proved "enum R<T, E> { Good(T), Bad(E) }\n\nstruct int_int { x: int }\n\nfn a() -> R<int, int_int>\n  ensures result == Good(5)\n{\n  Good(5)\n}\n\nfn b() -> R<int_int, int>\n  ensures result == Bad(5)\n{\n  Bad(5)\n}\n"
    typeError "enum R<T, E> { Good(T), Bad(E) }\n\nstruct int_int { x: int }\n\nfn b() -> R<int_int, int> {\n  Good(5)\n}\n" "expected"

[<Fact>]
let ``a function named like a builtin does not change the generated Python`` () =
    let src = "fn divmod(a: int, b: int) -> (int, int)\n  ensures result == (0, 0)\n{\n  (0, 0)\n}\n\nfn ord(c: char) -> int\n  ensures result == 0\n{\n  0\n}\n\nfn chr(c: int) -> int\n  ensures result == 0\n{\n  0\n}\n\nfn half(n: int) -> int\n  ensures result == n / 2\n{\n  n / 2\n}\n\nfn code_of(c: char) -> int\n  ensures result == code(c)\n{\n  code(c)\n}\n"
    Assert.Equal("3 97", pythonOf src "import main; print(main.half(7), main.code_of('a'))" false)

[<Fact>]
let ``a reserved word in Python cannot meet another name`` () =
    Assert.Equal("1", pythonOf "fn f() -> int\n  ensures result == 1\n{\n  let class = 3;\n  let class_ = 2;\n  class - class_\n}\n" "import main; print(main.f())" false)

[<Fact>]
let ``a struct checks what it holds, in depth`` () =
    let src = "struct Bag { xs: seq<nat>, ys: seq<i32> }\n\nfn f(b: Bag) -> int\n  ensures result == len(b.xs)\n{\n  len(b.xs)\n}\n"
    Assert.Contains("out of the bounds", pythonOf src "import main\ntry:\n  main.Bag([-5], [])\nexcept ValueError as e: print(e)" false)
    Assert.Contains("out of the bounds", pythonOf src "import main\ntry:\n  main.Bag([], [2**40])\nexcept ValueError as e: print(e)" false)

[<Fact>]
let ``with runtime checks, what relies on an unproved function is checked too`` () =
    let src = "fn dec(n: nat) -> nat {\n  n - 1\n}\n\nfn wrong(x: int) -> int\n  ensures result == x + 1\n{\n  assert dec(0) == 0;\n  x\n}\n"
    Assert.Contains("Error", pythonOf src "import main; print(main.wrong(5))" true)

[<Fact>]
let ``run_by with runtime checks does not loop`` () =
    let src = "fn f(x: int) -> int\n  run_by g\n{\n  x\n}\n\nfn g(x: int) -> int\n  ensures result == f(x)\n{\n  x + 1\n}\n"
    let out = pythonOf src "import main; print(main.f(1))" true
    Assert.DoesNotContain("RecursionError", out)

[<Fact>]
let ``csharp: a copy of a generic can hold a type of the file`` () =
    withFiles [ "main", "import option\n\nstruct Pt { x: i32 }\n\nfn f(p: Pt) -> option.Option<Pt>\n  ensures result == option.Some(p)\n{\n  option.Some(p)\n}\n" ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (CSharp { Namespace = "N"; CheckAllRequires = false }) (Path.Combine(dir, "main.quod")) typed r false with
            | Ok g ->
                let text = g.Imported |> List.find (fun (m, _) -> m = "option") |> snd
                Assert.Contains("Main.Pt", text)
                Assert.Contains("public abstract class Option_Pt", text)
            | Result.Error why -> failwith why
        | other -> failwithf "%A" other)

[<Fact>]
let ``python: a name of a variable does not hide a case or a struct`` () =
    let src = "enum Tree { Leaf, Node(int) }\nstruct Pt { x: int }\n\nfn is_leaf(t: Tree, Leaf: int) -> bool\n  ensures result == match t { Leaf => true, Node(_) => false }\n{\n  match t { Leaf => true, _ => false }\n}\n\nfn probe() -> bool\n  ensures result\n{\n  is_leaf(Leaf, 0)\n}\n\nfn build(v: int) -> Pt\n  ensures result.x == v\n{\n  let Pt: int = v;\n  Pt(Pt)\n}\n\nfn inner(t: Tree) -> int\n  ensures result == match t { Node(Leaf) => Leaf, Leaf => 0 }\n{\n  match t { Node(Leaf) => Leaf, Leaf => 0 }\n}\n"
    Assert.Equal("True 4 7", pythonOf src "import main; print(main.probe(), main.build(4).x, main.inner(main.Node(7)))" false)

[<Fact>]
let ``python: a list read from a value cannot change it`` () =
    let src = "struct Grid { rows: seq<seq<nat>> }\n\nfn first(g: Grid) -> bool\n  requires len(g.rows) > 0 && len(g.rows[0]) > 0\n  ensures result\n{\n  g.rows[0][0] >= 0\n}\n\nfn longer(g: Grid) -> seq<seq<nat>>\n  ensures result == g.rows + [[1]]\n{\n  g.rows + [[1]]\n}\n"
    Assert.Contains("TypeError", pythonOf src "import main; g = main.Grid([[1]]); g.rows[0][0] = -1" false)
    Assert.Contains("TypeError", pythonOf src "import main; g = main.Grid([[1]]); g.rows.append([])" false)
    Assert.Equal("[[1], [1], 2] True", pythonOf src "import main; g = main.Grid([[1]]); r = main.longer(g); r.append(2); print(r, main.first(g))" false)

let private unprovedTypes = "fn scale(x: i32) -> i32 {\n  x * 1000\n}\n\nfn shrink(n: nat) -> nat {\n  n - 1\n}\n\nfn minus(x: i32) -> i32 {\n  -x\n}\n\nfn narrow(x: int) -> i32 {\n  to_i32(x)\n}\n\nfn letter(x: int) -> char {\n  char_of(x)\n}\n"

[<Fact>]
let ``with runtime checks, what a type promises is checked`` () =
    for call in [ "scale(2**30)"; "shrink(0)"; "minus(-2**31)"; "narrow(2**40)"; "letter(0xD800)" ] do
        Assert.Contains("(not proved by quod", pythonOf unprovedTypes ("import main; print(main." + call + ")") true)
    Assert.Equal("3000 3 -5 3 a", pythonOf unprovedTypes "import main; print(main.scale(3), main.shrink(4), main.minus(5), main.narrow(3), main.letter(97))" true)

[<Fact>]
let ``with runtime checks, a proved function is not called against its requires`` () =
    let src = "fn half(n: int) -> int\n  requires n >= 0\n  ensures result == n / 2\n{\n  n / 2\n}\n\nfn wrong(x: int) -> int {\n  half(x - 5)\n}\n"
    Assert.Contains("precondition", pythonOf src "import main; print(main.wrong(1))" true)

[<Fact>]
let ``csharp: with runtime checks, what a type promises is computed without bounds, then checked`` () =
    withFiles [ "main", unprovedTypes ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (CSharp { Namespace = "N"; CheckAllRequires = false }) (Path.Combine(dir, "main.quod")) typed r true with
            | Ok g ->
                Assert.Contains("_quod_fit32(checked((long)x * (long)1000))", g.Code)
                Assert.Contains("_quod_fit_nat(", g.Code)
                Assert.Contains("_quod_fit_char(", g.Code)
            | Result.Error why -> failwith why
        | other -> failwithf "%A" other)

[<Fact>]
let ``csharp: a generic struct has the name of its copy`` () =
    withFiles [ "main", "struct Box<T> { v: T }\n\nfn one() -> Box<int>\n  ensures result == Box(1)\n{\n  Box(1)\n}\n" ] (fun dir outcome ->
        match outcome with
        | Checked(typed, r) ->
            match generate (CSharp { Namespace = "N"; CheckAllRequires = false }) (Path.Combine(dir, "main.quod")) typed r false with
            | Ok g ->
                Assert.Contains("public sealed class Box_int : IEquatable<Box_int>", g.Code)
                Assert.Contains("public Box_int(long v)", g.Code)
            | Result.Error why -> failwith why
        | other -> failwithf "%A" other)

[<Fact>]
let ``a lemma cannot be generic, and says so`` () =
    typeError "lemma same<T>(a: T)\n{\n}\n" "a lemma cannot be generic"

[<Fact>]
let ``csharp: a type named like its file does not name the class`` () =
    let build (files: (string * string) list) (check: Generated -> unit) =
        withFiles files (fun dir outcome ->
            match outcome with
            | Checked(typed, r) ->
                match generate (CSharp { Namespace = "N"; CheckAllRequires = false }) (Path.Combine(dir, "main.quod")) typed r false with
                | Ok g -> check g
                | Result.Error why -> failwith why
            | other -> failwithf "%A" other)
    let money = "struct Money { cents: i64 }\n\nfn zero() -> Money\n  ensures result.cents == 0\n{\n  Money(0)\n}\n"
    build [ "money", money; "main", "import money\n\nfn none() -> money.Money\n  ensures result.cents == 0\n{\n  money.zero()\n}\n" ] (fun g ->
        Assert.Contains("MoneyModule.Money None()", g.Code)
        Assert.Contains("MoneyModule.Zero()", g.Code)
        let text = g.Imported |> List.find (fun (m, _) -> m = "money") |> snd
        Assert.Contains("public static class MoneyModule", text)
        Assert.Contains("public sealed class Money ", text))
    build [ "main", "struct Main { x: i32 }\n\nfn make() -> Main\n  ensures result.x == 1\n{\n  Main(1)\n}\n" ] (fun g ->
        Assert.Contains("public static class MainModule", g.Code))

[<Fact>]
let ``a case of another module is named in full, and the message says so`` () =
    let lib = "enum Answer { Yes(int), Nope }\n"
    rejectedWith "built by its full name, 'lib.Yes'" "main.quod" [ "lib", lib; "main", "import lib\n\nfn f() -> lib.Answer\n  ensures result == lib.Yes(1)\n{\n  Yes(1)\n}\n" ]
    rejectedWith "built by its full name, 'lib.Nope'" "main.quod" [ "lib", lib; "main", "import lib\n\nfn f() -> lib.Answer\n  ensures result == lib.Nope\n{\n  Nope\n}\n" ]

[<Fact>]
let ``a literal in the cases of a match takes the bounded type its context wants`` () =
    let src = "enum C { A, B(nat), D }\n\nfn p(c: C) -> i32\n  ensures result == match c { A => 0, B(y) => if y >= 5 { 10 } else { 5 }, D => 30 }\n{\n  match c { A => 0, B(y) => if y >= 5 { 10 } else { 5 }, D => 30 }\n}\n\nfn q(c: C, x: i32) -> i32\n  requires 0 <= x <= 100\n  ensures result == x - x * p(c) / 100\n{\n  let k: i32 = match c { A => 0, B(y) => if y >= 5 { 10 } else { 5 }, _ => 30 };\n  x - x * k / 100\n}\n"
    Assert.Equal("90 0 70", pythonOf src "import main; print(main.q(main.B(5), 100), main.q(main.A(), 0), main.q(main.D(), 100))" false)
    typeError "enum C { A, B }\n\nfn p(c: C) -> i32\n  ensures result == 3000000000\n{\n  match c { A => 3000000000, B => 1 }\n}\n" "does not fit in i32"
