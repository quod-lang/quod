/// C# backend: one static class per Quod file, from the typed representation of a *verified*
/// program. The code stays within C# 7.3 and the standard library, for .NET Framework 4.7.2 as for
/// .NET Core. Proved contracts produce no code, except the cheap `requires` at the public boundary:
/// a C# caller proves nothing. Design: docs/design/backend-csharp.fr.md.
module Quod.CodegenCSharp

open System
open System.Collections.Generic
open System.Numerics
open System.Text
open System.Text.RegularExpressions
open Quod.Typed

type Options =
    { Namespace: string
      /// Check the quantified `requires` at the public boundary too (--check-requires all).
      CheckAllRequires: bool }

let defaultOptions = { Namespace = "Quod.Generated"; CheckAllRequires = false }

let private reserved =
    set [ "abstract"; "as"; "base"; "bool"; "break"; "byte"; "case"; "catch"; "char"; "checked"; "class"; "const"
          "continue"; "decimal"; "default"; "delegate"; "do"; "double"; "else"; "enum"; "event"; "explicit"; "extern"
          "false"; "finally"; "fixed"; "float"; "for"; "foreach"; "goto"; "if"; "implicit"; "in"; "int"; "interface"
          "internal"; "is"; "lock"; "long"; "namespace"; "new"; "null"; "object"; "operator"; "out"; "override"
          "params"; "private"; "protected"; "public"; "readonly"; "ref"; "return"; "sbyte"; "sealed"; "short"; "sizeof"
          "stackalloc"; "static"; "string"; "struct"; "switch"; "this"; "throw"; "true"; "try"; "typeof"; "uint"
          "ulong"; "unchecked"; "unsafe"; "ushort"; "using"; "virtual"; "void"; "volatile"; "while"; "_" ]

let private csName (n: string) =
    if reserved.Contains n then "@" + n
    elif n.StartsWith "_quod_" then n + "_"
    else n

/// `binary_search` -> `BinarySearch`: the public name of a function, or the class of a file.
let pascal (n: string) =
    // `first__int`, a copy of a generic, must stay apart from a function named `first_int`
    let one (part: string) =
        let parts = Regex.Split(part, "[^A-Za-z0-9]+") |> Array.filter (fun p -> p <> "")
        parts |> Array.map (fun p -> string (Char.ToUpperInvariant p.[0]) + p.Substring 1) |> String.concat ""
    let joined = n.Split([| "__" |], StringSplitOptions.None) |> Array.map one |> String.concat "_"
    if joined.Trim('_') = "" then "_" elif Char.IsDigit joined.[0] then "_" + joined else joined

/// The class that a file generates; its functions are its methods and its types are nested in it, and
/// C# cannot name either like it: `Money` in `money.quod` is `MoneyModule.Money`.
let private classNameOf (file: string) (publicNames: string list) (typeNames: string list) =
    let name = pascal (IO.Path.GetFileNameWithoutExtension file)
    if List.contains name publicNames || List.contains name typeNames then name + "Module" else name

/// The file `quod build` writes.
let outputFile (file: string) = pascal (IO.Path.GetFileNameWithoutExtension file) + ".g.cs"

/// What Quod code calls: never equal to a public name, a parameter or a local.
let private implName (f: string) = "_quod_f_" + f

/// The class of the file being generated, for a copy of a generic of another module that holds one of
/// its types: `Option<Pt>` lives in `Option`, and `Pt` in the file (review of 0.3).
let private rootClass = new System.Threading.ThreadLocal<string>(fun () -> "")

/// The class of each imported module of the program being generated, for its types.
let private moduleClass = new System.Threading.ThreadLocal<Map<string, string>>(fun () -> Map.empty)

/// A copy has `__` in its name, for the compiler: `Option__int` is `Option_int` to a C# reader. Should two
/// fall on one name, the C# compiler says so.
let private dataShort (name: string) = (shortName name).Replace("__", "_")

let rec csType (t: Ty) =
    match t with
    | TyInt | TyNat | TyError -> "BigInteger"
    | TyBool -> "bool"
    // inside, a scalar value: C#'s char is a UTF-16 unit, and half an emoji is not a character
    | TyChar | TyI32 -> "int"
    | TyI64 -> "long"
    | TyData d ->
        // through its module's class, which holds it
        match Quod.Modules.split d.DataName with
        | Some m, n -> defaultArg (moduleClass.Value.TryFind m) (pascal m) + "." + n.Replace("__", "_")
        | None, n -> (if rootClass.Value = "" then "" else rootClass.Value + ".") + n.Replace("__", "_")
    | TySeq e -> "IReadOnlyList<" + csType e + ">"
    | TyTuple ts -> "(" + (ts |> List.map csType |> String.concat ", ") + ")"

let rec private hasChar (t: Ty) =
    match t with
    | TyChar -> true
    | TySeq e -> hasChar e
    | TyTuple ts -> List.exists hasChar ts
    | _ -> false

/// The type a C# caller sees: `string` for a string, and an `int` for a char, its scalar value.
let rec private publicType (t: Ty) =
    match t with
    | TySeq TyChar -> "string"
    | TySeq e -> "IReadOnlyList<" + publicType e + ">"
    | TyTuple ts -> "(" + (ts |> List.map publicType |> String.concat ", ") + ")"
    | t -> csType t

/// An argument from a caller as Quod's values: validated, since a lone surrogate is not a character.
let rec private fromCaller (t: Ty) (term: string) (depth: int) : string =
    match t with
    | TyChar -> "_quod_char(" + term + ")"
    | TySeq TyChar -> "_quod_str(" + term + ")"
    | TySeq e when hasChar e ->
        let x = "_quod_x" + string depth
        "new _QuodView<" + publicType e + ", " + csType e + ">(" + term + ", " + x + " => " + fromCaller e x (depth + 1) + ")"
    | TyTuple ts when hasChar t ->
        "(" + (ts |> List.mapi (fun k c -> fromCaller c (term + ".Item" + string (k + 1)) depth) |> String.concat ", ") + ")"
    | _ -> term

let rec private holdsList (t: Ty) =
    match t with
    | TySeq _ -> true
    | TyTuple ts -> List.exists holdsList ts
    | _ -> false

/// Does a value of this type keep a list inside a class, which outlives the call?
let rec private dataHoldsList (t: Ty) =
    match t with
    | TyData d -> d.DataCases |> List.exists (fun c -> c.Fields |> List.exists (fun (_, ft) -> holdsList ft || dataHoldsList ft))
    | TySeq e -> dataHoldsList e
    | TyTuple ts -> List.exists dataHoldsList ts
    | _ -> false

/// A list of the caller's that a value will keep, copied: the caller's `list[0] = 9` must not change
/// what was proved, and a class promises to be immutable. A string is converted already.
let rec private frozen (t: Ty) (term: string) (depth: int) : string =
    match t with
    | TySeq TyChar -> term
    | TySeq e when holdsList e ->
        let x = "_quod_c" + string depth
        "_quod_copy_of(" + term + ", " + x + " => " + frozen e x (depth + 1) + ")"
    | TySeq _ -> "_quod_copy(" + term + ")"
    | TyTuple ts when holdsList t ->
        let x = "_quod_c" + string depth
        "_quod_with(" + term + ", " + x + " => (" + (ts |> List.mapi (fun k c -> frozen c (x + ".Item" + string (k + 1)) (depth + 1)) |> String.concat ", ") + "))"
    | _ -> term

/// A value read by a caller: a list of its own cannot be cast back to what the value holds.
let rec private exposed (t: Ty) (term: string) (depth: int) : string =
    match t with
    | TySeq TyChar -> "_quod_text(" + term + ")"
    | TySeq e ->
        let x = "_quod_e" + string depth
        "new _QuodView<" + csType e + ", " + publicType e + ">(" + term + ", " + x + " => " + exposed e x (depth + 1) + ")"
    | TyTuple ts when holdsList t ->
        let x = "_quod_e" + string depth
        "_quod_with(" + term + ", " + x + " => (" + (ts |> List.mapi (fun k c -> exposed c (x + ".Item" + string (k + 1)) (depth + 1)) |> String.concat ", ") + "))"
    | _ -> term

/// The hash of a value, on what it is made of.
let rec private hashOf (t: Ty) (term: string) (depth: int) : string =
    match t with
    | TySeq e ->
        let x = "_quod_h" + string depth
        "_quod_hash(" + term + ", " + x + " => " + hashOf e x (depth + 1) + ")"
    | TyTuple ts ->
        let x = "_quod_h" + string depth
        "_quod_with(" + term + ", " + x + " => " + (ts |> List.mapi (fun k c -> hashOf c (x + ".Item" + string (k + 1)) (depth + 1)) |> List.fold (fun acc h -> "(" + acc + " * 31 + " + h + ")") "17") + ")"
    | _ -> term + ".GetHashCode()"

/// A result of Quod's as the caller's.
let rec private toCaller (t: Ty) (term: string) (depth: int) : string =
    match t with
    | TySeq TyChar -> "_quod_text(" + term + ")"
    | TySeq e when hasChar e ->
        let x = "_quod_x" + string depth
        "new _QuodView<" + csType e + ", " + publicType e + ">(" + term + ", " + x + " => " + toCaller e x (depth + 1) + ")"
    | TyTuple ts when hasChar t ->
        // once: the tuple may be a call
        "_quod_with(" + term + ", _quod_t" + string depth + " => (" + (ts |> List.mapi (fun k c -> toCaller c ("_quod_t" + string depth + ".Item" + string (k + 1)) (depth + 1)) |> String.concat ", ") + "))"
    | _ -> term

/// The empty literal has an unknown element type (`seq<error>`): what surrounds it knows it.
let rec private merge (known: Ty) (other: Ty) =
    match known, other with
    | TyError, t -> t
    | TySeq a, TySeq b -> TySeq(merge a b)
    | TyTuple xs, TyTuple ys when xs.Length = ys.Length -> TyTuple(List.map2 merge xs ys)
    | t, _ -> t

/// Equal under Quod's rules with no C# type difference: nat is int.
let rec private shape (t: Ty) =
    match t with
    | TyNat | TyError -> TyInt
    | TySeq e -> TySeq(shape e)
    | TyTuple ts -> TyTuple(List.map shape ts)
    | t -> t

/// The class of a case: the struct itself, or nested in its enum.
let private caseClass (d: DataDecl) (k: int) =
    if d.IsStruct then csType (TyData d) else csType (TyData d) + "." + shortName d.DataCases.[k].CaseName

let private literal (text: string) = "\"" + text.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""

let private xml (text: string) = text.Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;")

let private helpers =
    [ "text",
      "private static IReadOnlyList<int> _quod_str(string s)
        {
            if (s == null) throw new ArgumentNullException(\"s\");
            var r = new List<int>(s.Length);
            for (int i = 0; i < s.Length; i++)
            {
                if (char.IsHighSurrogate(s[i]) && i + 1 < s.Length && char.IsLowSurrogate(s[i + 1])) { r.Add(char.ConvertToUtf32(s[i], s[i + 1])); i++; }
                else if (char.IsSurrogate(s[i])) throw new ArgumentException(\"a lone surrogate is not a character\");
                else r.Add(s[i]);
            }
            return r;
        }

        private static int _quod_char(int c)
        {
            if (c < 0 || c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF)) throw new ArgumentException(\"not a Unicode scalar value: \" + c);
            return c;
        }

        private static string _quod_text(IReadOnlyList<int> xs)
        {
            var b = new System.Text.StringBuilder(xs.Count);
            for (int i = 0; i < xs.Count; i++) b.Append(char.ConvertFromUtf32(xs[i]));
            return b.ToString();
        }
"
      // in a function checked at run time: without a proof, nothing else says what a type promises
      "fit",
      "private static int _quod_fit32(BigInteger v)
        {
            if (v < int.MinValue || v > int.MaxValue) throw new QuodContractException(\"the value \" + v + \" does not fit in i32 (not proved by quod: checked at run time)\");
            return (int)v;
        }

        private static long _quod_fit64(BigInteger v)
        {
            if (v < long.MinValue || v > long.MaxValue) throw new QuodContractException(\"the value \" + v + \" does not fit in i64 (not proved by quod: checked at run time)\");
            return (long)v;
        }

        private static BigInteger _quod_fit_nat(BigInteger v)
        {
            if (v.Sign < 0) throw new QuodContractException(\"the value \" + v + \" is not a nat (not proved by quod: checked at run time)\");
            return v;
        }

        private static int _quod_fit_char(BigInteger v)
        {
            if (v.Sign < 0 || v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF)) throw new QuodContractException(\"the value \" + v + \" is not a Unicode scalar value (not proved by quod: checked at run time)\");
            return (int)v;
        }"
      "with", "private static R _quod_with<T, R>(T x, Func<T, R> f) { return f(x); }"
      "hash",
      "private static int _quod_hash<T>(IReadOnlyList<T> xs, Func<T, int> f)
        {
            int h = xs.Count;
            for (int i = 0; i < xs.Count; i++) h = unchecked(h * 31 + f(xs[i]));
            return h;
        }"
      "copy",
      "private static IReadOnlyList<T> _quod_copy<T>(IReadOnlyList<T> xs)
        {
            if (xs == null) throw new ArgumentNullException(\"xs\");
            var r = new T[xs.Count];
            for (int i = 0; i < r.Length; i++) r[i] = xs[i];
            return r;
        }

        private static IReadOnlyList<T> _quod_copy_of<T>(IReadOnlyList<T> xs, Func<T, T> f)
        {
            if (xs == null) throw new ArgumentNullException(\"xs\");
            var r = new T[xs.Count];
            for (int i = 0; i < r.Length; i++) r[i] = f(xs[i]);
            return r;
        }"
      "seq", "private static IReadOnlyList<T> _quod_seq<T>(params T[] xs) { return xs; }"
      "concat",
      "private static IReadOnlyList<T> _quod_concat<T>(IReadOnlyList<T> a, IReadOnlyList<T> b)
        {
            var r = new List<T>(a.Count + b.Count);
            r.AddRange(a);
            r.AddRange(b);
            return r;
        }"
      "slice",
      "private static IReadOnlyList<T> _quod_slice<T>(IReadOnlyList<T> xs, BigInteger lo, BigInteger hi)
        {
            if (lo < 0 || lo > hi || hi > xs.Count) throw new IndexOutOfRangeException(\"slice \" + lo + \"..\" + hi + \" out of bounds\");
            var r = new T[(int)(hi - lo)];
            for (int i = 0; i < r.Length; i++) r[i] = xs[(int)lo + i];
            return r;
        }"
      "mod",
      "// Euclidean division, as in Quod and SMT-LIB: the remainder is always >= 0.
        private static BigInteger _quod_mod(BigInteger a, BigInteger b)
        {
            BigInteger r = BigInteger.Remainder(a, b);
            return r.Sign < 0 ? r + BigInteger.Abs(b) : r;
        }"
      "div", "private static BigInteger _quod_div(BigInteger a, BigInteger b) { return BigInteger.Divide(a - _quod_mod(a, b), b); }"
      // C# truncates, and Quod's division is Euclidean. int.MinValue % -1 throws in .NET, though its result is 0.
      "mod32", "private static int _quod_mod32(int a, int b) { if (b == -1) return 0; int r = a % b; return r >= 0 ? r : (b < 0 ? r - b : r + b); }"
      "div32", "private static int _quod_div32(int a, int b) { if (b == -1) return -a; int q = a / b; return a % b >= 0 ? q : (b < 0 ? q + 1 : q - 1); }"
      "mod64", "private static long _quod_mod64(long a, long b) { if (b == -1) return 0; long r = a % b; return r >= 0 ? r : (b < 0 ? r - b : r + b); }"
      "div64", "private static long _quod_div64(long a, long b) { if (b == -1) return -a; long q = a / b; return a % b >= 0 ? q : (b < 0 ? q + 1 : q - 1); }"
      "all",
      "private static bool _quod_all(BigInteger lo, BigInteger hi, Func<BigInteger, bool> f)
        {
            for (BigInteger i = lo; i < hi; i = i + 1) if (!f(i)) return false;
            return true;
        }"
      "any",
      "private static bool _quod_any(BigInteger lo, BigInteger hi, Func<BigInteger, bool> f)
        {
            for (BigInteger i = lo; i < hi; i = i + 1) if (f(i)) return true;
            return false;
        }"
      "every",
      "private static bool _quod_every<T>(IEnumerable<T> xs, Func<T, bool> f)
        {
            foreach (var x in xs) if (!f(x)) return false;
            return true;
        }"
      "view",
      "// A list of the caller's integers, seen as Quod's: nothing is copied, each element is converted when read.
        private sealed class _QuodView<TFrom, T> : IReadOnlyList<T>
        {
            private readonly IReadOnlyList<TFrom> xs;
            private readonly Func<TFrom, T> convert;
            public _QuodView(IReadOnlyList<TFrom> xs, Func<TFrom, T> convert)
            {
                if (xs == null) throw new ArgumentNullException(\"xs\");
                this.xs = xs;
                this.convert = convert;
            }
            public int Count { get { return xs.Count; } }
            public T this[int i] { get { return convert(xs[i]); } }
            public IEnumerator<T> GetEnumerator() { foreach (var x in xs) yield return convert(x); }
            System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() { return GetEnumerator(); }
        }"
      "show",
      "private static string _quod_show(object v)
        {
            if (v is bool) return (bool)v ? \"true\" : \"false\";
            var items = v as System.Collections.IEnumerable;
            if (items == null) return Convert.ToString(v);
            var parts = new List<string>();
            foreach (var x in items) parts.Add(_quod_show(x));
            return \"[\" + string.Join(\", \", parts) + \"]\";
        }" ]

type private Gen(checks: Set<string>) =
    let used = HashSet<string>() // helpers
    let constants = SortedDictionary<BigInteger, string>()
    let eqs = Dictionary<Ty, string>()
    let eqOrder = ResizeArray<Ty>()
    /// Names and types in scope. C# refuses `if c { let x = 1; } let x = 1;`, which Quod accepts:
    /// every declaration of a function gets a name of its own.
    let mutable names: Map<string, string> = Map.empty
    let mutable types: Map<string, Ty> = Map.empty
    let taken = HashSet<string>()
    let mutable inPlace: Set<string> = Set.empty

    member _.Used = used

    /// Is the function being generated checked at run time (--runtime-checks)?
    member val Checking = false with get, set

    /// The integer constants of the class: `BigInteger.One` or `_quod_2`, not `new BigInteger(2)` at each use.
    member _.Constant(n: BigInteger) =
        if n.IsZero then "BigInteger.Zero"
        elif n.IsOne then "BigInteger.One"
        else
            let name = "_quod_" + (if n.Sign < 0 then "minus_" else "") + BigInteger.Abs(n).ToString()
            constants.[n] <- name
            name

    member _.ConstantFields() : string list =
        [ for KeyValue(n, name) in constants ->
              let value =
                  if n >= BigInteger Int64.MinValue && n <= BigInteger Int64.MaxValue then "new BigInteger(" + n.ToString() + ")"
                  else "BigInteger.Parse(\"" + n.ToString() + "\")"
              "private static readonly BigInteger " + name + " = " + value + ";" ]

    member _.Reset() =
        names <- Map.empty
        types <- Map.empty
        taken.Clear()

    member _.Bind(name: string, ty: Ty) : string =
        let baseName = csName name
        let mutable candidate = baseName
        let mutable k = 2
        while not (taken.Add candidate) do
            candidate <- baseName + "_" + string k
            k <- k + 1
        names <- names.Add(name, candidate)
        types <- types.Add(name, ty)
        candidate

    member _.Scoped(work: unit -> unit) =
        let n, t = names, types
        work ()
        names <- n
        types <- t

    member _.Name(n: string) = match names.TryFind n with Some c -> c | None -> csName n

    member g.Help(name: string) =
        used.Add name |> ignore
        if name = "div" then used.Add "mod" |> ignore
        "_quod_" + name

    /// The function that compares two values of a type, field by field: `==` compares references.
    member g.EqName(t: Ty) =
        let t = shape t
        match eqs.TryGetValue t with
        | true, n -> n
        | _ ->
            let n = "_quod_eq_" + string (eqs.Count + 1)
            eqs.[t] <- n
            eqOrder.Add t
            match t with
            | TySeq e -> if shape e <> TyInt && e <> TyBool then g.EqName e |> ignore
            | TyTuple ts -> for x in ts do if shape x <> TyInt && x <> TyBool then g.EqName x |> ignore
            | _ -> ()
            n

    member g.Eq(t: Ty, a: string, b: string) =
        match shape t with
        | TyInt | TyBool | TyI32 | TyI64 | TyChar -> "(" + a + " == " + b + ")"
        | TyData _ -> a + ".Equals(" + b + ")"
        | s -> g.EqName s + "(" + a + ", " + b + ")"

    member g.EqFunctions() : string list =
        [ for t in eqOrder do
              let ct = csType t
              let body =
                  match t with
                  | TySeq e ->
                      "if (a.Count != b.Count) return false;\n            for (int i = 0; i < a.Count; i++) if (!"
                      + g.Eq(e, "a[i]", "b[i]") + ") return false;\n            return true;"
                  | TyTuple ts ->
                      "return " + (ts |> List.mapi (fun k x -> g.Eq(x, "a.Item" + string (k + 1), "b.Item" + string (k + 1))) |> String.concat " && ") + ";"
                  | TyData _ -> "return a.Equals(b);"
                  | _ -> "return a == b;"
              "private static bool " + eqs.[t] + "(" + ct + " a, " + ct + " b)\n        {\n            " + body + "\n        }" ]

    /// An expression, whose type is `want` where the expression itself does not know it.
    member g.Expr(e: TExpr, want: Ty) : string =
        let ty = merge (shape e.Ty) (shape want)
        let elem = match ty with TySeq t -> t | _ -> TyInt
        match e.Kind with
        | EInt n when e.Ty = TyChar || e.Ty = TyI32 -> n.ToString()
        | EInt n when e.Ty = TyI64 -> n.ToString() + "L"
        | EInt n -> g.Constant n
        | EBool b -> if b then "true" else "false"
        | EVar n -> g.Name n
        | EResult -> "_quod_result"
        // a string literal stays one in the generated code
        | ESeq xs when e.Ty = TySeq TyChar && not xs.IsEmpty
                       && xs |> List.forall (fun x -> match x.Kind with EInt n -> n >= bigint 32 && n <> bigint 127 | _ -> false) ->
            g.Help "text" |> ignore
            let text = xs |> List.map (fun x -> match x.Kind with EInt n -> Char.ConvertFromUtf32(int n) | _ -> "") |> String.concat ""
            "_quod_str(" + literal text + ")"
        | ESeq xs ->
            let elem = xs |> List.fold (fun acc x -> merge acc (shape x.Ty)) elem
            g.Help "seq" + "<" + csType elem + ">(" + (xs |> List.map (fun x -> g.Expr(x, elem)) |> String.concat ", ") + ")"
        | ETuple xs ->
            let parts = match ty with TyTuple ts when ts.Length = xs.Length -> ts | _ -> xs |> List.map (fun x -> x.Ty)
            "(" + (List.map2 (fun x t -> g.Expr(x, t)) xs parts |> String.concat ", ") + ")"
        | EIndex(s, i) -> g.Expr(s, TySeq ty) + "[(int)" + g.Expr(i, TyInt) + "]"
        | ESlice(s, lo, hi) ->
            let sv = g.Expr(s, ty)
            g.Help "slice" + "<" + csType elem + ">(" + sv + ", "
            + (lo |> Option.map (fun x -> g.Expr(x, TyInt)) |> Option.defaultValue "BigInteger.Zero") + ", "
            + (hi |> Option.map (fun x -> g.Expr(x, TyInt)) |> Option.defaultValue ("new BigInteger(" + sv + ".Count)")) + ")"
        | EProj(t, k) -> g.Expr(t, t.Ty) + ".Item" + string (k + 1)
        | ECons(k, xs) ->
            match e.Ty with
            | TyData d ->
                let case = d.DataCases.[k]
                caseClass d k + "._quod_make(" + (List.map2 (fun (x: TExpr) (_, t: Ty) -> g.Expr(x, t)) xs case.Fields |> String.concat ", ") + ")"
            | _ -> failwith "a value of no data type"
        | EField(a, k, i) ->
            match a.Ty with
            | TyData d when not d.IsStruct -> "((" + caseClass d k + ")" + g.Expr(a, a.Ty) + ")._f" + string i
            | _ -> g.Expr(a, a.Ty) + "._f" + string i
        | EMatch(s, arms) ->
            match s.Ty with
            | TyData d ->
                let mutable text = ""
                g.Scoped(fun () ->
                    let m = g.Bind("_quod_m", s.Ty)
                    let arm (k: int, names: string list, body: TExpr) =
                        let rec bind (i: int) (rest: string list) : string =
                            match rest with
                            | [] -> g.Expr(body, ty)
                            | "_" :: tail -> bind (i + 1) tail
                            | n :: tail ->
                                let ft = snd d.DataCases.[k].Fields.[i]
                                let mutable inner = ""
                                let field = "((" + caseClass d k + ")" + m + ")._f" + string i
                                g.Scoped(fun () ->
                                    let local = g.Bind(n, ft)
                                    inner <- g.Help "with" + "(" + field + ", " + local + " => " + bind (i + 1) tail + ")")
                                inner
                        bind 0 names
                    let rec chain (xs: (int * string list * TExpr) list) =
                        match xs with
                        | [ x ] -> arm x
                        | ((k, _, _) as x) :: rest -> "(" + m + " is " + caseClass d k + " ? " + arm x + " : " + chain rest + ")"
                        | [] -> failwith "a match without a case"
                    text <- g.Help "with" + "(" + g.Expr(s, s.Ty) + ", " + m + " => " + chain arms + ")")
                text
            | _ -> failwith "a match on no data type"
        | ELen s -> "new BigInteger(" + g.Expr(s, s.Ty) + ".Count)"
        | ECall(f, args) -> g.Call(f, args)
        // computed without bounds: C# would wrap, in silence, a value that no proof says fits
        | ENeg _ | EArith _ when g.Checking && isBounded e.Ty ->
            g.Help "fit" |> ignore
            (if e.Ty = TyI32 then "_quod_fit32(" else "_quod_fit64(") + g.Expr({ e with Ty = TyInt }, TyInt) + ")"
        | ENeg x when isBounded x.Ty && not (isBounded e.Ty) -> "(-new BigInteger(" + g.Expr(x, x.Ty) + "))"
        | ENeg x -> "(-" + g.Expr(x, TyInt) + ")"
        | ENot { Kind = EEq(a, b) } when (match shape (merge (shape a.Ty) (shape b.Ty)) with TyInt | TyBool -> true | _ -> false) ->
            "(" + g.Expr(a, a.Ty) + " != " + g.Expr(b, b.Ty) + ")"
        | ENot x -> "(!" + g.Expr(x, TyBool) + ")"
        | EArith(op, a, b) ->
            // an operation in int on bounded operands (a contract) must not be computed in C#'s int
            let wide (o: TExpr) = if isBounded o.Ty && not (isBounded e.Ty) then "new BigInteger(" + g.Expr(o, o.Ty) + ")" else g.Expr(o, TyInt)
            let x, y = wide a, wide b
            let euclid (name: string) =
                let name = match e.Ty with TyI32 -> name + "32" | TyI64 -> name + "64" | _ -> name
                g.Help name + "(" + x + ", " + y + ")"
            match op with
            | OAdd -> "(" + x + " + " + y + ")"
            | OSub -> "(" + x + " - " + y + ")"
            | OMul -> "(" + x + " * " + y + ")"
            | ODiv -> euclid "div"
            | OMod -> euclid "mod"
        | EConcat(a, b) ->
            let t = merge (merge ty (shape a.Ty)) (shape b.Ty)
            let elem = match t with TySeq x -> x | _ -> TyInt
            g.Help "concat" + "<" + csType elem + ">(" + g.Expr(a, t) + ", " + g.Expr(b, t) + ")"
        | ECmp(op, a, b) ->
            let o = match op with OLt -> "<" | OLe -> "<=" | OGt -> ">" | OGe -> ">="
            "(" + g.Expr(a, TyInt) + " " + o + " " + g.Expr(b, TyInt) + ")"
        | EEq(a, b) when isBounded a.Ty || isBounded b.Ty -> "(" + g.Expr(a, a.Ty) + " == " + g.Expr(b, b.Ty) + ")"
        | EEq(a, b) ->
            let t = merge (shape a.Ty) (shape b.Ty)
            g.Eq(t, g.Expr(a, t), g.Expr(b, t))
        | ELogic(op, a, b) ->
            let x, y = g.Expr(a, TyBool), g.Expr(b, TyBool)
            match op with
            | OAnd -> "(" + x + " && " + y + ")"
            | OOr -> "(" + x + " || " + y + ")"
            | OImplies -> "(!" + x + " || " + y + ")"
            | OIff -> "(" + x + " == " + y + ")"
        | EIf(c, a, b) ->
            let t = merge (merge ty (shape a.Ty)) (shape b.Ty)
            "(" + g.Expr(c, TyBool) + " ? " + g.Expr(a, t) + " : " + g.Expr(b, t) + ")"
        | EQuant(q, v, lo, hi, body) ->
            let f = match q with Syntax.Forall -> g.Help "all" | Syntax.Exists -> g.Help "any"
            let l, h = g.Expr(lo, TyInt), g.Expr(hi, TyInt)
            let mutable text = ""
            g.Scoped(fun () ->
                let name = g.Bind(v, TyInt)
                text <- f + "(" + l + ", " + h + ", " + name + " => " + g.Expr(body, TyBool) + ")")
            text
        | EToNat x when g.Checking -> g.Help "fit" + "_nat(" + g.Expr(x, TyInt) + ")"
        | EToNat x -> g.Expr(x, TyInt)
        | EConvert x when g.Checking && e.Ty <> TyNat ->
            let name = match e.Ty with TyChar -> "_char(" | TyI32 -> "32(" | _ -> "64("
            g.Help "fit" + name + g.Expr(x, TyInt) + ")"
        | EConvert x when e.Ty = TyChar || e.Ty = TyI32 -> "((int)" + g.Expr(x, TyInt) + ")"
        | EConvert x when e.Ty = TyI64 -> "((long)" + g.Expr(x, TyInt) + ")"
        | EConvert x -> "new BigInteger(" + g.Expr(x, TyChar) + ")"

    /// The parameter types of the program, for arguments that do not know theirs (`f([])`).
    member val Signatures: Map<string, TFn> = Map.empty with get, set

    /// The class of each imported module, for a call to its public method.
    member val ModuleClasses: Map<string, string> = Map.empty with get, set

    /// The public method of a function of another module.
    member val ModuleMethod: string -> string -> string = (fun _ h -> pascal h) with get, set

    member g.Call(f: string, args: TExpr list) : string =
        let ps = g.Signatures.[f].Params
        let callee =
            match Quod.Modules.split f with
            | Some m, h ->
                // a module's own values go through: a string is converted once, at the outer boundary
                let target = g.Signatures.[f]
                let raw = hasChar target.Ret || target.Params |> List.exists (fun p -> hasChar p.Ty)
                g.ModuleClasses.[m] + "." + (if raw then "_quod_pub_" + h else g.ModuleMethod m h)
            | None, _ -> implName f
        callee + "(" + (List.map2 (fun (a: TExpr) (p: TParam) -> g.Expr(a, p.Ty)) args ps |> String.concat ", ") + ")"

    /// A condition that holds when `e` does not: `b == 0`, not `!(b != 0)`.
    member g.Negated(e: TExpr) =
        match e.Kind with
        | ENot { Kind = EEq(a, b) } when (match shape (merge (shape a.Ty) (shape b.Ty)) with TyInt | TyBool -> true | _ -> false) ->
            "(" + g.Expr(a, a.Ty) + " == " + g.Expr(b, b.Ty) + ")"
        | ENot x -> g.Expr(x, TyBool)
        | _ -> "!" + g.Expr(e, TyBool)

    /// The test that a value's `nat`s are `>= 0`, None if it has none to test. Under a sequence,
    /// only when `deep`: it costs a pass over it, like a quantified requires.
    member g.NatTest(t: Ty, term: string, deep: bool, depth: int) : string option =
        match t with
        | TyNat -> Some("(" + term + ".Sign >= 0)")
        | TySeq e when deep ->
            let x = "_quod_n" + string depth
            g.NatTest(e, x, deep, depth + 1)
            |> Option.map (fun inner ->
                g.Help "every" |> ignore
                "_quod_every<" + csType e + ">(" + term + ", " + x + " => " + inner + ")")
        | TyTuple ts ->
            match ts |> List.mapi (fun k c -> g.NatTest(c, term + ".Item" + string (k + 1), deep, depth)) |> List.choose id with
            | [] -> None
            | tests -> Some("(" + String.Join(" && ", tests) + ")")
        | _ -> None

    member g.Check(sb: StringBuilder, indent: string, e: TExpr, what: string, f: TFn) =
        let values =
            (f.Params |> List.map (fun p -> p.Name, g.Name p.Name))
            @ (if what = "postcondition" then [ "result", "_quod_result" ] else [])
            |> List.mapi (fun k (n, cs) ->
                g.Help "show" |> ignore
                literal ((if k = 0 then "; " else ", ") + n + " = ") + " + _quod_show(" + cs + ")")
        let message =
            literal (f.Name + ": " + what + " `" + Printer.exprText (toSyntax e) + "` does not hold (not proved by quod: checked at run time)")
            :: values
        sb.Append(indent).Append("if (!").Append(g.Expr(e, TyBool)).Append(") throw new QuodContractException(")
          .Append(String.Join(" + ", message)).Append(");\n") |> ignore

    member g.Block(sb: StringBuilder, indent: string, items: TStmt list, f: TFn) =
        g.Scoped(fun () -> for s in items do g.Stmt(sb, indent, s, f))

    member g.Stmt(sb: StringBuilder, indent: string, s: TStmt, f: TFn) =
        let line (text: string) = sb.Append(indent).Append(text).Append('\n') |> ignore
        let checked' = checks.Contains f.Name
        let elemOf t = match t with TySeq e -> e | _ -> TyInt
        match s.Kind with
        | SLet(_, n, _, _) when isLemmaBinding n -> () // a proof step: erased
        | SLet(_, n, ty, v) when inPlace.Contains n ->
            let value = g.Expr(v, ty)
            let name = g.Bind(n, ty)
            line ("List<" + csType (elemOf ty) + "> " + name + " = new List<" + csType (elemOf ty) + ">(" + value + ");")
        | SLet(_, n, ty, v) ->
            let value = g.Expr(v, ty)
            let name = g.Bind(n, ty)
            line (csType ty + " " + name + " = " + value + ";")
        | SAssign(n, { Kind = EConcat({ Kind = EVar n2 }, tail) }) when n2 = n && inPlace.Contains n ->
            match tail.Kind with
            | ESeq [ x ] -> line (g.Name n + ".Add(" + g.Expr(x, elemOf types.[n]) + ");")
            | _ -> line (g.Name n + ".AddRange(" + g.Expr(tail, types.[n]) + ");")
        | SAssign(n, v) when inPlace.Contains n ->
            line (g.Name n + " = new List<" + csType (elemOf types.[n]) + ">(" + g.Expr(v, types.[n]) + ");")
        | SAssign(n, v) -> line (g.Name n + " = " + g.Expr(v, types.[n]) + ";")
        | SIf(c, a, b) ->
            line ("if (" + g.Expr(c, TyBool) + ")")
            line "{"
            g.Block(sb, indent + "    ", a, f)
            line "}"
            if not b.IsEmpty then
                line "else"
                line "{"
                g.Block(sb, indent + "    ", b, f)
                line "}"
        | SWhile(c, invs, _, body) ->
            line ("while (" + g.Expr(c, TyBool) + ")")
            line "{"
            // invariants hold before every iteration and after the last one
            if checked' then for inv in invs do g.Check(sb, indent + "    ", inv, "invariant", f)
            g.Block(sb, indent + "    ", body, f)
            line "}"
            if checked' then for inv in invs do g.Check(sb, indent, inv, "invariant", f)
        | SAssert e -> if checked' then g.Check(sb, indent, e, "assertion", f)
        | SReturn e ->
            if checked' && not f.Ensures.IsEmpty then
                line "{"
                line ("    " + csType f.Ret + " _quod_result = " + g.Expr(e, f.Ret) + ";")
                for ens in f.Ensures do g.Check(sb, indent + "    ", ens, "postcondition", f)
                line "    return _quod_result;"
                line "}"
            else
                line ("return " + g.Expr(e, f.Ret) + ";")

    member g.SetInPlace(s: Set<string>) = inPlace <- s

/// Does the end of these statements never get reached, in the eyes of the C# compiler?
let rec private returns (items: TStmt list) =
    items |> List.exists (fun s ->
        match s.Kind with
        | SReturn _ -> true
        | SIf(_, a, b) -> returns a && returns b
        | _ -> false)

/// Is there a list of integers in this type, which a caller would hold as `int` or `long`?
let rec private hasIntegerList (t: Ty) =
    let rec hasInteger t =
        match t with
        | TyInt | TyNat -> true
        | TySeq e -> hasInteger e
        | TyTuple ts -> List.exists hasInteger ts
        | _ -> false
    match t with
    | TySeq e -> hasInteger e
    | TyTuple ts -> List.exists hasIntegerList ts
    | _ -> false

let rec private narrowType (narrow: string) (t: Ty) =
    match t with
    | TyInt | TyNat | TyError -> narrow
    | TyBool | TyChar | TyI32 | TyI64 | TyData _ -> csType t
    | TySeq e -> "IReadOnlyList<" + narrowType narrow e + ">"
    | TyTuple ts -> "(" + (ts |> List.map (narrowType narrow) |> String.concat ", ") + ")"

/// A value of the narrow type as Quod's. Exact, since int and long fit in a BigInteger. `depth` names
/// the lambdas apart.
let rec private widen (narrow: string) (t: Ty) (term: string) (depth: int) : string =
    match t with
    | TyInt | TyNat | TyError -> "new BigInteger(" + term + ")"
    | TyBool | TyChar | TyI32 | TyI64 | TyData _ -> term
    | TySeq e ->
        let x = "_quod_x" + string depth
        "new _QuodView<" + narrowType narrow e + ", " + csType e + ">(" + term + ", " + x + " => " + widen narrow e x (depth + 1) + ")"
    | TyTuple ts ->
        "(" + (ts |> List.mapi (fun k c -> widen narrow c (term + ".Item" + string (k + 1)) depth) |> String.concat ", ") + ")"

/// The class of each imported module of a flattened program.
let private moduleClasses (whole: TProgram) : Map<string, string> =
    Codegen.importedModules whole
    |> List.map (fun m ->
        let names = whole.Fns |> List.filter (fun f -> not f.IsLemma && not f.IsPrivate && fst (Quod.Modules.split f.Name) = Some m) |> List.map (fun f -> pascal (snd (Quod.Modules.split f.Name)))
        let types = whole.Types |> List.filter (fun d -> fst (Quod.Modules.split d.DataName) = Some m) |> List.map (fun d -> dataShort d.DataName)
        m, classNameOf m names types)
    |> Map.ofList

/// Set while the modules of a file are generated.
let setRootClass (file: string) (whole: TProgram) =
    let view = Codegen.moduleView None whole
    moduleClass.Value <- moduleClasses whole
    let methods =
        view.Fns
        |> List.filter (fun f -> not f.IsLemma && not f.IsPrivate)
        |> List.map (fun f -> let m = pascal f.Name in if view.Types |> List.exists (fun d -> dataShort d.DataName = m) then m + "Of" else m)
    rootClass.Value <- classNameOf file methods (view.Types |> List.map (fun d -> dataShort d.DataName))

let clearRootClass () =
    rootClass.Value <- ""
    moduleClass.Value <- Map.empty

/// The C# of a verified program, or why it cannot be generated. `checks` lists the functions whose
/// proofs did not all pass (built only with --runtime-checks): their contracts run at run time.
let rec generate (sourceFile: string) (prog: TProgram) (checks: Set<string>) (options: Options) : Result<string, string> =
    generateIn sourceFile prog prog checks options

/// The same, for one module (`prog`) of a flattened program (`whole`), whose other modules it calls.
and generateIn (sourceFile: string) (prog: TProgram) (whole: TProgram) (checks: Set<string>) (options: Options) : Result<string, string> =
    let fns = prog.Fns |> List.filter (fun f -> not f.IsLemma)
    // a function `level` and a type `Level` are natural in Quod, and C# cannot hold both in a class
    let methodIn (types: DataDecl list) (name: string) =
        let m = pascal name
        if types |> List.exists (fun d -> dataShort d.DataName = m) then m + "Of" else m
    let methodOf = methodIn prog.Types
    let publicNames = fns |> List.filter (fun f -> not f.IsPrivate) |> List.map (fun f -> methodOf f.Name)
    let clash = fns |> List.groupBy (fun f -> methodOf f.Name) |> List.tryFind (fun (_, g) -> g.Length > 1)
    match clash with
    | Some(p, g) ->
        Result.Error("not built: " + (g |> List.map (fun f -> "'" + f.Name + "'") |> String.concat " and ")
                     + " would both be the C# method '" + p + "': rename one")
    | None when not (Regex.IsMatch(options.Namespace, @"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")) ->
        Result.Error("not built: '" + options.Namespace + "' is not a C# namespace")
    | None ->
        let g = Gen(checks)
        // names as this module calls them: its own short, the others in full
        g.Signatures <- (whole.Fns |> List.map (fun f -> f.Name, f)) @ (prog.Fns |> List.map (fun f -> f.Name, f)) |> Map.ofList
        g.ModuleMethod <- (fun m h -> methodIn (whole.Types |> List.filter (fun d -> fst (Quod.Modules.split d.DataName) = Some m)) h)
        g.ModuleClasses <- moduleClasses whole
        let sb = StringBuilder()
        let indent = "        "
        for f in fns do
            // a function checked at run time runs as written; and a run_by whose loop is checked would call itself
            let f = if checks.Contains f.Name || (match f.RunBy with Some g -> checks.Contains g | None -> false) then f else Codegen.tailToLoop f
            let ps = f.Params |> List.map (fun p -> csType p.Ty + " " + csName p.Name) |> String.concat ", "
            let isChecked = checks.Contains f.Name
            let boundary = f.Requires |> List.filter (fun r -> match r.Kind with EBool true -> false | _ -> true)
            let enforced, left = boundary |> List.partition (fun r -> options.CheckAllRequires || Codegen.cheap r)
            let text (e: TExpr) = Printer.exprText (toSyntax e)
            let realSb = sb
            // a private function has only its implementation: what follows is dropped
            let sb = if f.IsPrivate then StringBuilder() else realSb
            // the public method: what a C# caller sees and what it cannot be trusted with
            sb.Append(indent).Append("/// <summary>")
              .Append(if isChecked then "NOT fully proved: contracts are checked at run time." else "Proved by quod.")
              .Append("</summary>\n") |> ignore
            let notes =
                [ for r in enforced -> "requires " + text r + " (checked)"
                  for e in f.Ensures -> "ensures " + text e
                  for l in Option.toList f.Loose -> "loose (" + l.Left + ", " + l.Right + ") => " + text l.Relation
                  for r in left -> "NOT CHECKED, the caller's duty, unless QUOD_CHECK_REQUIRES is defined: requires " + text r
                  if not options.CheckAllRequires then
                      for p in f.Params |> List.filter (fun p -> Codegen.natInList p.Ty) ->
                          "NOT CHECKED, the caller's duty, unless QUOD_CHECK_REQUIRES is defined: every integer of " + p.Name + " is >= 0" ]
            if not notes.IsEmpty then
                sb.Append(indent).Append("/// <remarks>\n") |> ignore
                for n in notes do sb.Append(indent).Append("/// ").Append(xml n).Append("<br/>\n") |> ignore
                sb.Append(indent).Append("/// </remarks>\n") |> ignore
            // with a string in the signature, the method below takes Quod's values, and another one
            // converts the caller's. A call from another module has no need to convert twice.
            let text' = hasChar f.Ret || f.Params |> List.exists (fun p -> hasChar p.Ty)
            let body = indent + "    "
            if text' then
                g.Help "text" |> ignore
                g.Help "with" |> ignore
                let rec viewed (t: Ty) =
                    match t with
                    | TySeq TyChar -> false
                    | TySeq e -> hasChar e
                    | TyTuple ts -> List.exists viewed ts
                    | _ -> false
                if viewed f.Ret || f.Params |> List.exists (fun p -> viewed p.Ty) then g.Help "view" |> ignore
                let outer = f.Params |> List.map (fun p -> publicType p.Ty + " " + csName p.Name) |> String.concat ", "
                let call = "_quod_pub_" + f.Name + "(" + (f.Params |> List.map (fun p -> fromCaller p.Ty (csName p.Name) 0) |> String.concat ", ") + ")"
                sb.Append(indent).Append("public static ").Append(publicType f.Ret).Append(' ').Append(methodOf f.Name).Append('(').Append(outer).Append(")\n")
                  .Append(indent).Append("{\n")
                  .Append(body).Append("return ").Append(toCaller f.Ret call 0).Append(";\n")
                  .Append(indent).Append("}\n\n") |> ignore
            let publicName = if text' then "_quod_pub_" + f.Name else methodOf f.Name
            sb.Append(indent).Append(if text' then "internal static " else "public static ").Append(csType f.Ret).Append(' ').Append(publicName).Append('(').Append(ps).Append(")\n")
              .Append(indent).Append("{\n") |> ignore
            g.Reset()
            for p in f.Params do g.Bind(p.Name, p.Ty) |> ignore
            for p in f.Params do
                match p.Ty with
                | TySeq _ | TyData _ ->
                    let n = csName p.Name
                    sb.Append(body).Append("if (").Append(n).Append(" == null) throw new ArgumentNullException(\"").Append(p.Name).Append("\");\n") |> ignore
                | _ -> ()
            // a `nat` is a requires the proofs rely on: `n >= 0` (review of 0.1.5)
            let natCheck (deep: bool) (p: TParam) =
                match g.NatTest(p.Ty, csName p.Name, deep, 0) with
                | Some test ->
                    sb.Append(body).Append("if (!").Append(test).Append(") throw new ArgumentException(")
                      .Append(literal (f.Name + ": argument " + p.Name + " must be >= 0")).Append(");\n") |> ignore
                | None -> ()
            for p in f.Params do natCheck options.CheckAllRequires p
            for r in enforced do
                sb.Append(body).Append("if (").Append(g.Negated r).Append(") throw new ArgumentException(")
                  .Append(literal (f.Name + ": requires " + text r)).Append(");\n") |> ignore
            // the file is compiled in the calling project, whose symbol turns these on, at their cost
            let natLists = if options.CheckAllRequires then [] else f.Params |> List.filter (fun p -> Codegen.natInList p.Ty)
            if not left.IsEmpty || not natLists.IsEmpty then
                sb.Append("#if QUOD_CHECK_REQUIRES\n") |> ignore
                for p in natLists do natCheck true p
                for r in left do
                    sb.Append(body).Append("if (!").Append(g.Expr(r, TyBool)).Append(") throw new ArgumentException(")
                      .Append(literal (f.Name + ": requires " + text r)).Append(");\n") |> ignore
                sb.Append("#endif\n") |> ignore
            // a class in the result may keep a list given here, and outlive this call
            let keeps = dataHoldsList f.Ret
            if keeps && f.Params |> List.exists (fun p -> holdsList p.Ty) then
                g.Help "copy" |> ignore
                g.Help "with" |> ignore
            let impl = implName f.Name + "(" + (f.Params |> List.map (fun p -> if keeps then frozen p.Ty (csName p.Name) 0 else csName p.Name) |> String.concat ", ") + ")"
            // a list read from a class may be the one it holds
            let guarded = not prog.Types.IsEmpty && holdsList f.Ret && not text'
            if guarded then
                g.Help "view" |> ignore
                g.Help "text" |> ignore
                g.Help "with" |> ignore
            sb.Append(body).Append("return ").Append(if guarded then exposed f.Ret impl 0 else impl).Append(";\n")
              .Append(indent).Append("}\n\n") |> ignore
            // a real caller has a List<int>, not an IReadOnlyList<BigInteger>: the same method for
            // its integers, without a copy (review of 0.1.4). The result stays a BigInteger.
            if not text' && f.Params |> List.exists (fun p -> hasIntegerList p.Ty) then
                for narrow in [ "int"; "long" ] do
                    let narrowed = f.Params |> List.map (fun p -> narrowType narrow p.Ty + " " + csName p.Name) |> String.concat ", "
                    g.Help "view" |> ignore
                    sb.Append(indent).Append("/// <summary>The same for a list of ").Append(narrow).Append(": it is not copied. See the method above.</summary>\n")
                      .Append(indent).Append("public static ").Append(csType f.Ret).Append(' ').Append(methodOf f.Name).Append('(').Append(narrowed).Append(")\n")
                      .Append(indent).Append("{\n")
                      .Append(body).Append("return ").Append(methodOf f.Name).Append('(')
                      .Append(f.Params |> List.map (fun p -> widen narrow p.Ty (csName p.Name) 0) |> String.concat ", ").Append(");\n")
                      .Append(indent).Append("}\n\n") |> ignore
            // the implementation, which Quod code calls
            let sb = realSb
            g.Checking <- isChecked
            sb.Append(indent).Append("private static ").Append(csType f.Ret).Append(' ').Append(implName f.Name).Append('(').Append(ps).Append(")\n")
              .Append(indent).Append("{\n") |> ignore
            if f.IsRecursive then
                sb.Append(body).Append("RuntimeHelpers.EnsureSufficientExecutionStack();\n") |> ignore
            if isChecked then
                for r in f.Requires do g.Check(sb, body, r, "precondition", f)
            match f.Body with
            | TExprBody e ->
                g.SetInPlace Set.empty
                g.Stmt(sb, body, { Kind = SReturn e; Span = e.Span }, f)
            | TStmtBody items ->
                g.SetInPlace(Codegen.appendable items isChecked)
                g.Block(sb, body, items, f)
                if not (returns items) then
                    sb.Append(body).Append("throw new InvalidOperationException(\"unreachable: the function was proved to return\");\n") |> ignore
            sb.Append(indent).Append("}\n\n") |> ignore
            g.Checking <- false
        // the structs and enums: immutable classes, equal by their values. Quod holds its own
        // representation in `_f0`; a C# caller builds and reads through what checks and converts.
        let dataText = StringBuilder()
        for d in prog.Types do
            let inner = if d.IsStruct then indent else indent + "    "
            let dataName = dataShort d.DataName
            if not d.IsStruct then
                dataText.Append(indent).Append("public abstract class ").Append(dataName).Append("\n").Append(indent).Append("{\n")
                        .Append(inner).Append("private ").Append(dataName).Append("() { }\n\n") |> ignore
            for c in d.DataCases do
                // a struct is its type: a copy of a generic has the name of the copy
                let name = if d.IsStruct then dataName else shortName c.CaseName
                let i2 = inner + "    "
                let i3 = i2 + "    "
                let fields = c.Fields |> List.indexed
                let raw = fields |> List.map (fun (i, (_, t)) -> csType t + " f" + string i)
                let args = fields |> List.map (fun (i, _) -> "f" + string i)
                let member' (field: string) = (let p = pascal field in if p = name then p + "Value" else p)
                let param' (field: string) = (let n = csName field in if n = "_quod_raw" then n + "_" else n)
                dataText.Append(inner).Append("public sealed class ").Append(name).Append(if d.IsStruct then " : IEquatable<" + name + ">" else " : " + dataName + ", IEquatable<" + name + ">").Append("\n").Append(inner).Append("{\n") |> ignore
                for i, (_, t) in fields do
                    dataText.Append(i2).Append("internal readonly ").Append(csType t).Append(" _f").Append(i).Append(";\n") |> ignore
                dataText.Append(i2).Append("private ").Append(name).Append("(").Append(String.Join(", ", raw @ [ "bool _quod_raw" ])).Append(")\n").Append(i2).Append("{\n") |> ignore
                for i, _ in fields do
                    dataText.Append(i3).Append("_f").Append(i).Append(" = f").Append(i).Append(";\n") |> ignore
                dataText.Append(i2).Append("}\n\n") |> ignore
                dataText.Append(i2).Append("internal static ").Append(dataName).Append(" _quod_make(").Append(String.Join(", ", raw)).Append(") { return new ").Append(name).Append("(").Append(String.Join(", ", args @ [ "true" ])).Append("); }\n\n") |> ignore
                // what the caller sees
                let publicParams = fields |> List.map (fun (_, (f, t)) -> publicType t + " " + param' f)
                let converted = fields |> List.map (fun (_, (f, t)) -> frozen t (fromCaller t (param' f) 0) 0)
                if fields |> List.exists (fun (_, (_, t)) -> holdsList t) then
                    g.Help "copy" |> ignore
                    g.Help "with" |> ignore
                if fields |> List.exists (fun (_, (_, t)) -> hasChar t) then
                    g.Help "text" |> ignore
                    g.Help "with" |> ignore
                    g.Help "view" |> ignore
                dataText.Append(i2).Append("public ").Append(name).Append("(").Append(String.Join(", ", publicParams)).Append(") : this(").Append(String.Join(", ", converted @ [ "true" ])).Append(")\n").Append(i2).Append("{\n") |> ignore
                for _, (f, t) in fields do
                    match t with
                    | TySeq _ | TyData _ -> dataText.Append(i3).Append("if (").Append(param' f).Append(" == null) throw new ArgumentNullException(\"").Append(f).Append("\");\n") |> ignore
                    | _ -> ()
                    // what a value holds outlives the call: checked in depth, the copy goes through it anyway
                    match g.NatTest(t, param' f, true, 0) with
                    | Some test -> dataText.Append(i3).Append("if (!").Append(test).Append(") throw new ArgumentException(").Append(literal (name + ": field " + f + " must be >= 0")).Append(");\n") |> ignore
                    | None -> ()
                dataText.Append(i2).Append("}\n\n") |> ignore
                for i, (f, t) in fields do
                    if holdsList t then
                        g.Help "view" |> ignore
                        g.Help "text" |> ignore
                        g.Help "with" |> ignore
                    dataText.Append(i2).Append("public ").Append(publicType t).Append(' ').Append(member' f).Append(" { get { return ").Append(exposed t ("_f" + string i) 0).Append("; } }\n") |> ignore
                let tests = fields |> List.map (fun (i, (_, t)) -> g.Eq(t, "_f" + string i, "x._f" + string i))
                dataText.Append(if fields.IsEmpty then "" else "\n")
                        .Append(i2).Append("public bool Equals(").Append(name).Append(" x) { return !ReferenceEquals(x, null)").Append(String.Join("", tests |> List.map (fun t -> " && " + t))).Append("; }\n")
                        .Append(i2).Append("public override bool Equals(object o) { return Equals(o as ").Append(name).Append("); }\n") |> ignore
                if fields |> List.exists (fun (_, (_, t)) -> holdsList t) then g.Help "hash" |> ignore; g.Help "with" |> ignore
                let hashed = fields |> List.map (fun (i, (_, t)) -> hashOf t ("_f" + string i) 0)
                // on what it is made of, once: the value does not change
                dataText.Append(i2).Append("private int _quod_hashed;\n")
                        .Append(i2).Append("public override int GetHashCode() { if (_quod_hashed == 0) _quod_hashed = unchecked(").Append(List.fold (fun acc h -> "(" + acc + " * 31 + " + h + ")") (string (name.Length + 17)) hashed).Append(") | 1; return _quod_hashed; }\n") |> ignore
                if d.IsStruct then
                    dataText.Append("\n").Append(i2).Append("public static bool operator ==(").Append(name).Append(" a, ").Append(name).Append(" b) { return ReferenceEquals(a, b) || (!ReferenceEquals(a, null) && a.Equals(b)); }\n")
                            .Append(i2).Append("public static bool operator !=(").Append(name).Append(" a, ").Append(name).Append(" b) { return !(a == b); }\n") |> ignore
                dataText.Append(inner).Append("}\n\n") |> ignore
            if not d.IsStruct then
                // what a `match` gives Quod: a C# caller must say what to do in every case
                let handlers =
                    d.DataCases |> List.map (fun c ->
                        let short = shortName c.CaseName
                        "Func<" + String.Join(", ", (c.Fields |> List.map (fun (_, t) -> publicType t)) @ [ "R" ]) + "> on" + pascal short)
                dataText.Append(inner).Append("public R Match<R>(").Append(String.Join(", ", handlers)).Append(")\n").Append(inner).Append("{\n") |> ignore
                for c in d.DataCases do
                    let short = shortName c.CaseName
                    let reads = c.Fields |> List.map (fun (f, _) -> (let p = pascal f in if p = short then p + "Value" else p))
                    dataText.Append(inner).Append("    if (this is ").Append(short).Append(") { var c = (").Append(short).Append(")this; return on").Append(pascal short).Append("(")
                            .Append(String.Join(", ", reads |> List.map (fun r -> "c." + r))).Append("); }\n") |> ignore
                dataText.Append(inner).Append("    throw new InvalidOperationException(\"no other case\");\n").Append(inner).Append("}\n\n")
                        .Append(inner).Append("public static bool operator ==(").Append(dataName).Append(" a, ").Append(dataName).Append(" b) { return ReferenceEquals(a, b) || (!ReferenceEquals(a, null) && a.Equals(b)); }\n")
                        .Append(inner).Append("public static bool operator !=(").Append(dataName).Append(" a, ").Append(dataName).Append(" b) { return !(a == b); }\n")
                        .Append(inner).Append("public override bool Equals(object o) { return ReferenceEquals(this, o); }\n")
                        .Append(inner).Append("public override int GetHashCode() { return 0; }\n") |> ignore
                dataText.Append(indent).Append("}\n\n") |> ignore
        let eqFunctions = g.EqFunctions()
        let helperText =
            helpers
            |> List.filter (fun (name, _) -> g.Used.Contains name)
            |> List.map snd
        let lemmas = prog.Fns |> List.filter (fun f -> f.IsLemma) |> List.map (fun f -> f.Name)
        let out = StringBuilder()
        out.Append("// <auto-generated>Generated by quod ").Append(Quod.Diagnostics.quodVersion).Append(" from ")
           .Append(IO.Path.GetFileName sourceFile).Append(". Do not edit.</auto-generated>\n") |> ignore
        if checks.IsEmpty then out.Append("// Every contract below was proved; only cheap requires are checked, at the public boundary.\n") |> ignore
        else out.Append("// WARNING: not fully proved (--runtime-checks): ").Append(String.Join(", ", checks)).Append("\n") |> ignore
        if not lemmas.IsEmpty then
            out.Append("// Lemmas are proofs, not code, and are not generated: ").Append(String.Join(", ", lemmas)).Append("\n") |> ignore
        out.Append("#pragma warning disable\n")
           .Append("using System;\nusing System.Collections.Generic;\nusing System.Numerics;\nusing System.Runtime.CompilerServices;\n\n")
           .Append("namespace ").Append(options.Namespace).Append("\n{\n")
           .Append("    public static class ").Append(classNameOf sourceFile publicNames (prog.Types |> List.map (fun d -> dataShort d.DataName))).Append("\n    {\n") |> ignore
        if not checks.IsEmpty then
            out.Append("        public sealed class QuodContractException : Exception\n        {\n")
               .Append("            public QuodContractException(string message) : base(message) { }\n        }\n\n") |> ignore
        let constantFields = g.ConstantFields()
        if not constantFields.IsEmpty then
            out.Append(indent).Append(String.Join("\n" + indent, constantFields)).Append("\n\n") |> ignore
        out.Append(dataText).Append(sb) |> ignore
        for h in helperText @ eqFunctions do
            out.Append(indent).Append(h).Append("\n\n") |> ignore
        out.Length <- out.Length - 1
        out.Append("    }\n}\n") |> ignore
        Ok(out.ToString().Replace("\r\n", "\n"))
