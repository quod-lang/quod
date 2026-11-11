/// Evaluates Quod expressions on concrete values. Used to *confirm* what the solver proposes
/// (a completeness witness, a counterexample) without trusting the solver: contracts are always
/// computable, since quantifiers are bounded and the functions they call are expression
/// functions, which terminate (that is proved before they are used).
module Quod.Eval

open System
open System.Numerics
open Quod.Typed

type Value =
    | VInt of BigInteger
    | VBool of bool
    | VChar of int
    /// A value of a struct or a case of an enum: its name, and its fields.
    | VData of string * Value list
    | VSeq of Value list
    | VTuple of Value list
    /// A map and a set: entries in ascending order of key, without duplicates, so that equal values are equal terms.
    | VMap of (Value * Value) list
    | VSet of Value list

/// Raised when a value cannot be computed: an index out of bounds, a division by zero, a call
/// to a statement function, a quantifier over a huge range. The caller then confirms nothing.
exception CannotEvaluate of string

let isScalar (n: BigInteger) =
    n.Sign >= 0 && n <= BigInteger 0x10FFFF && not (n >= BigInteger 0xD800 && n <= BigInteger 0xDFFF)

/// Raised in checking mode when running a function breaks one of its proof obligations: the
/// label and position are those of the obligation in the verifier ("invariant #2 is preserved
/// by the loop body"...). A run is a real execution, so this is a confirmed counterexample.
exception Violation of string * Quod.Syntax.Span

/// A `return` while running a statement body.
exception Returned of Value * Quod.Syntax.Span

/// Bounded quantifiers over more values than this are not evaluated.
let private maxRange = BigInteger 100000

/// Calls nested deeper than this are not evaluated. Values are small (sequences of 50 elements
/// at most), and running random inputs meets non-terminating functions: a deeper limit
/// overflowed the stack.
let private maxDepth = 400

/// Euclidean division, as in SMT-LIB and in the Quod semantics: the remainder is >= 0.
let euclidDivMod (a: BigInteger) (b: BigInteger) =
    let q0 = BigInteger.Divide(a, b)
    let r0 = a - q0 * b
    if r0.Sign < 0 then
        if b.Sign > 0 then q0 - BigInteger.One, r0 + b else q0 + BigInteger.One, r0 - b
    else q0, r0

/// Run `work` on a thread with a large stack (256 MB): evaluating nested calls, up to maxDepth
/// of them, takes several big frames each, more than the 1 MB of an ordinary thread.
let withBigStack (work: unit -> 'a) : 'a =
    let mutable result = Unchecked.defaultof<'a>
    let mutable error: exn = null
    let thread =
        System.Threading.Thread(
            (fun () ->
                try result <- work ()
                with e -> error <- e),
            256 * 1024 * 1024)
    thread.Start()
    thread.Join()
    if not (isNull error) then raise error
    result

let private charText (c: int) =
    if c < 32 || c = 127 then "\\u{" + c.ToString "X" + "}" else Char.ConvertFromUtf32 c

/// The order of keys: numbers, chars and booleans by value, strings (sequences) one element after the other.
let rec compareValue (a: Value) (b: Value) : int =
    match a, b with
    | VInt x, VInt y -> compare x y
    | VChar x, VChar y -> compare x y
    | VBool x, VBool y -> compare x y
    | VSeq xs, VSeq ys ->
        let rec go (xs: Value list) (ys: Value list) =
            match xs, ys with
            | [], [] -> 0
            | [], _ -> -1
            | _, [] -> 1
            | x :: xt, y :: yt -> (match compareValue x y with 0 -> go xt yt | c -> c)
        go xs ys
    | VTuple xs, VTuple ys ->
        let rec go (xs: Value list) (ys: Value list) =
            match xs, ys with
            | x :: xt, y :: yt -> (match compareValue x y with 0 -> go xt yt | c -> c)
            | _ -> 0
        go xs ys
    // a struct: its fields in turn; two cases of an enum: by name, which is only a canonical order
    | VData(a, xs), VData(b, ys) ->
        match compare a b with
        | 0 ->
            let rec go (xs: Value list) (ys: Value list) =
                match xs, ys with
                | x :: xt, y :: yt -> (match compareValue x y with 0 -> go xt yt | c -> c)
                | _ -> 0
            go xs ys
        | c -> c
    | _ -> 0

let putEntry (entries: (Value * Value) list) (k: Value) (v: Value) =
    let before = entries |> List.filter (fun (k', _) -> compareValue k' k < 0)
    let after = entries |> List.filter (fun (k', _) -> compareValue k' k > 0)
    before @ [ k, v ] @ after

let addElement (items: Value list) (x: Value) =
    if items |> List.exists (fun y -> compareValue x y = 0) then items
    else (x :: items) |> List.sortWith compareValue

let rec valueText (v: Value) =
    match v with
    | VInt n -> n.ToString()
    | VBool b -> if b then "true" else "false"
    | VChar c -> "'" + charText c + "'"
    | VData(name, []) -> name
    | VData(name, xs) -> name + "(" + (xs |> List.map valueText |> String.concat ", ") + ")"
    | VSeq xs when not xs.IsEmpty && xs |> List.forall (function VChar _ -> true | _ -> false) ->
        "\"" + (xs |> List.map (function VChar c -> charText c | _ -> "") |> String.concat "") + "\""
    | VSeq xs -> "[" + (xs |> List.map valueText |> String.concat ", ") + "]"
    | VTuple xs -> "(" + (xs |> List.map valueText |> String.concat ", ") + ")"
    | VMap entries -> "{" + (entries |> List.map (fun (k, x) -> valueText k + ": " + valueText x) |> String.concat ", ") + "}"
    | VSet xs -> "{" + (xs |> List.map valueText |> String.concat ", ") + "}"

/// Evaluates expressions and runs functions. In checking mode, what would be an evaluation
/// error is a broken obligation (Violation): an index out of bounds, a division by zero, a
/// negative nat, a call outside its precondition; and running a statement function checks its
/// assertions, invariants, loop measures and postconditions.
type Evaluator(fns: Map<string, TFn>, checking: bool) =
    let mutable depth = 0
    let mutable steps = 0
    /// The functions being run (checking mode), innermost first, with their measure on entry.
    let mutable running: (TFn * BigInteger option) list = []
    /// The branches taken: (span of the `if`, value of its condition). Reported when no run
    /// broke an obligation: a branch no run took is where a bug may hide (first-user test).
    let taken = System.Collections.Generic.HashSet<Quod.Syntax.Span * bool>()
    /// The last result whose postconditions were checked: the value a broken postcondition is
    /// about (quod_run reports it).
    let mutable checkedResult: Value option = None

    member _.Taken = taken
    member _.CheckedResult = checkedResult

    new(fns: Map<string, TFn>) = Evaluator(fns, false)

    /// An evaluation error: a broken obligation in checking mode, else "cannot evaluate".
    member private _.Fail(label: string, span: Quod.Syntax.Span, reason: string) : 'a =
        if checking then raise (Violation(label, span)) else raise (CannotEvaluate reason)

    member ev.Expr(e: TExpr, env: Map<string, Value>) : Value =
        let go x = ev.Expr(x, env)
        let asInt x = match go x with VInt n -> n | _ -> raise (CannotEvaluate "not an int")
        let asBool x = match go x with VBool b -> b | _ -> raise (CannotEvaluate "not a bool")
        let asSeq x = match go x with VSeq s -> s | _ -> raise (CannotEvaluate "not a sequence")
        match e.Kind with
        | EInt n when e.Ty = TyChar -> VChar(int n)
        | ECons(k, xs) ->
            match e.Ty with
            | TyData d -> VData(d.DataCases.[k].CaseName, List.map go xs)
            | _ -> raise (CannotEvaluate "a value of no data type")
        | EField(a, _, i) ->
            match go a with
            | VData(_, xs) -> xs.[i]
            | _ -> raise (CannotEvaluate "not a struct")
        | EMatch(s, arms) ->
            match go s, s.Ty with
            | VData(name, xs), TyData d ->
                let k = d.DataCases |> List.findIndex (fun c -> c.CaseName = name)
                let _, names, body = arms |> List.find (fun (i, _, _) -> i = k)
                ev.Expr(body, List.fold2 (fun (m: Map<string, Value>) n x -> if n = "_" then m else m.Add(n, x)) env names xs)
            | _ -> raise (CannotEvaluate "not an enum")
        | EInt n -> VInt n
        | EBool b -> VBool b
        | EVar n ->
            match env.TryFind n with
            | Some v -> v
            | None -> raise (CannotEvaluate("unbound " + n))
        | EResult ->
            match env.TryFind "result" with
            | Some v -> v
            | None -> raise (CannotEvaluate "no result")
        | ESeq xs -> VSeq(xs |> List.map go)
        | ETuple xs -> VTuple(xs |> List.map go)
        | EIndex(s, i) ->
            let xs, k = asSeq s, asInt i
            if k.Sign < 0 || k >= BigInteger xs.Length then ev.Fail("index in bounds", e.Span, "index out of bounds")
            xs.[int k]
        | ESlice(s, lo, hi) ->
            let xs = asSeq s
            let l = lo |> Option.map asInt |> Option.defaultValue BigInteger.Zero
            let h = hi |> Option.map asInt |> Option.defaultValue (BigInteger xs.Length)
            if l.Sign < 0 || l > h || h > BigInteger xs.Length then
                ev.Fail("slice bounds (0 <= lo <= hi <= len)", e.Span, "slice out of bounds")
            VSeq(xs |> List.skip (int l) |> List.take (int (h - l)))
        | EProj(t, k) ->
            match go t with
            | VTuple xs -> xs.[k]
            | _ -> raise (CannotEvaluate "not a tuple")
        | ELen s ->
            match go s with
            | VSeq xs | VSet xs -> VInt(BigInteger xs.Length)
            | VMap entries -> VInt(BigInteger entries.Length)
            | _ -> raise (CannotEvaluate "not a sequence, a map or a set")
        | ECol(op, args) -> ev.Collection(e, op, args, env)
        | EQuantIn(q, name, col, body) ->
            let items = match go col with VSet xs -> xs | _ -> raise (CannotEvaluate "not a set")
            if BigInteger items.Length > maxRange then raise (CannotEvaluate "a quantifier over too many values")
            let test x = (match ev.Expr(body, env.Add(name, x)) with VBool b -> b | _ -> raise (CannotEvaluate "not a bool"))
            match q with
            | Syntax.Forall -> VBool(Seq.forall test items)
            | Syntax.Exists -> VBool(Seq.exists test items)
        | ECall(name, args) ->
            let f = fns.[name]
            let values = args |> List.map go
            match f.Body with
            | TStmtBody _ when not checking -> raise (CannotEvaluate("'" + name + "' is a statement function"))
            | _ when checking ->
                // the caller's obligation: the callee's precondition
                let callEnv = List.zip (f.Params |> List.map (fun p -> p.Name)) values |> Map.ofList
                for (r, k) in List.zip f.Requires [ 1 .. f.Requires.Length ] do
                    if ev.Holds(r, callEnv) = Some false then
                        raise (Violation("precondition of '" + name + "'" + (if f.Requires.Length > 1 then " (requires #" + string k + ")" else ""), e.Span))
                // a call inside the caller's recursive cycle must make the measure smaller: a
                // call that does not (f(j - 0)) would run forever, where the solver only times out
                match running, f.Decreases with
                | (caller, Some m0) :: _, Some d when caller.IsRecursive && caller.Cycle = f.Cycle ->
                    match ev.Expr(d, callEnv) with
                    | VInt m1 when m0.Sign < 0 || m1 >= m0 ->
                        raise (Violation("recursive call decreases the measure (and it stays >= 0)", e.Span))
                    | _ -> ()
                | _ -> ()
                // the callee's own obligations are its own: a failure inside it is not the caller's
                try ev.Run(f, values) with Violation _ -> raise (CannotEvaluate("'" + name + "' fails"))
            | TExprBody body ->
                depth <- depth + 1
                try
                    if depth > maxDepth then raise (CannotEvaluate "recursion too deep")
                    let callEnv = List.zip (f.Params |> List.map (fun p -> p.Name)) values |> Map.ofList
                    ev.Expr(body, callEnv)
                finally
                    depth <- depth - 1
            | TStmtBody _ -> raise (CannotEvaluate("'" + name + "' is a statement function"))
        | ENeg x -> ev.Fitting(e, -(asInt x))
        | ENot x -> VBool(not (asBool x))
        | EArith(op, a, b) ->
            let x, y = asInt a, asInt b
            match op with
            | OAdd -> ev.Fitting(e, x + y)
            | OSub -> ev.Fitting(e, x - y)
            | OMul -> ev.Fitting(e, x * y)
            | ODiv | OMod ->
                if y.IsZero then ev.Fail("divisor is not zero", b.Span, "division by zero")
                let q, r = euclidDivMod x y
                ev.Fitting(e, (if op = ODiv then q else r))
        | EConcat(a, b) -> VSeq(asSeq a @ asSeq b)
        | ECmp(op, a, b) ->
            // two chars compare by their scalar values
            let asNumber x = match go x with VChar c -> BigInteger c | VInt n -> n | _ -> raise (CannotEvaluate "not a number")
            let x, y = asNumber a, asNumber b
            VBool(match op with OLt -> x < y | OLe -> x <= y | OGt -> x > y | OGe -> x >= y)
        | EEq(a, b) -> VBool(go a = go b)
        | ELogic(op, a, b) ->
            match op with
            | OAnd -> VBool(asBool a && asBool b) // && and || short-circuit, as guards do in proofs
            | OOr -> VBool(asBool a || asBool b)
            | OImplies -> VBool(not (asBool a) || asBool b)
            | OIff -> VBool(asBool a = asBool b)
        | EIf(c, a, b) ->
            let v = asBool c
            taken.Add((e.Span, v)) |> ignore
            if v then go a else go b
        | EQuant(q, name, lo, hi, body) ->
            let l, h = asInt lo, asInt hi
            if h - l > maxRange then raise (CannotEvaluate "quantifier range too large")
            let values = if h <= l then Seq.empty else seq { for i in 0 .. int (h - l) - 1 -> l + BigInteger i }
            let test (i: BigInteger) = match ev.Expr(body, env.Add(name, VInt i)) with VBool b -> b | _ -> false
            match q with
            | Syntax.Forall -> VBool(Seq.forall test values)
            | Syntax.Exists -> VBool(Seq.exists test values)
        | EConvert x when isBounded e.Ty -> ev.Fitting(e, asInt x)
        | EConvert x ->
            match go x with
            | VChar c -> VInt(BigInteger c)
            | VInt n when isScalar n -> VChar(int n)
            | VInt _ when checking -> raise (Violation("the argument of char_of is a Unicode scalar value", e.Span))
            | _ -> raise (CannotEvaluate "char_of of a value that is not a scalar value")
        | EToNat x ->
            let v = go x
            match v with
            | VInt n when checking && n.Sign < 0 -> raise (Violation("value is a nat (>= 0)", e.Span))
            | _ -> v

    /// A result in code of a bounded type must fit: running it is a real execution, so leaving the
    /// bounds is a confirmed counterexample.
    member ev.Fitting(e: TExpr, n: BigInteger) : Value =
        match boundsOf e.Ty with
        | Some(lo, hi) when n < lo || n > hi ->
            let what = match e.Kind with EConvert _ -> "the value" | _ -> "the result"
            if checking then raise (Violation(what + " fits in " + tyText e.Ty, e.Span))
            raise (CannotEvaluate "a result out of its bounds")
        | _ -> VInt n

    /// Is the value of the expected type (a nat is >= 0, recursively)?
    member ev.Fits(t: Ty, v: Value) : bool =
        match t, v with
        | TyNat, VInt n -> n.Sign >= 0
        | TyChar, VChar c -> isScalar (BigInteger c)
        | TyData d, VData(name, xs) ->
            d.DataCases |> List.exists (fun c -> c.CaseName = name && c.Fields.Length = xs.Length && List.forall2 (fun (_, t) x -> ev.Fits(t, x)) c.Fields xs)
        | TyInt, VInt _ -> true
        | (TyI32 | TyI64), VInt n -> (let lo, hi = (boundsOf t).Value in lo <= n && n <= hi)
        | TyBool, VBool _ -> true
        | TySeq e, VSeq xs -> xs |> List.forall (fun x -> ev.Fits(e, x))
        | TyTuple ts, VTuple xs when ts.Length = xs.Length -> List.forall2 (fun t x -> ev.Fits(t, x)) ts xs
        | TyMap(kt, vt), VMap entries -> entries |> List.forall (fun (k, x) -> ev.Fits(kt, k) && ev.Fits(vt, x))
        | TySet t, VSet xs -> xs |> List.forall (fun x -> ev.Fits(t, x))
        | _ -> false

    /// An operation on a map or a set. A read of a key that is not there is a broken obligation.
    member private ev.Collection(e: TExpr, op: ColOp, args: TExpr list, env: Map<string, Value>) : Value =
        let go x = ev.Expr(x, env)
        let entries x = match go x with VMap m -> m | _ -> raise (CannotEvaluate "not a map")
        let items x = match go x with VSet s -> s | _ -> raise (CannotEvaluate "not a set")
        match op, args with
        | MapOf, [ s ] ->
            match go s with
            | VSeq pairs -> VMap(pairs |> List.fold (fun m p -> match p with VTuple [ k; v ] -> putEntry m k v | _ -> raise (CannotEvaluate "not a pair")) [])
            | _ -> raise (CannotEvaluate "not a sequence")
        | SetOf, [ s ] ->
            match go s with
            | VSeq xs -> VSet(xs |> List.fold addElement [])
            | _ -> raise (CannotEvaluate "not a sequence")
        | Put, [ m; k; v ] -> VMap(putEntry (entries m) (go k) (go v))
        | MapRemove, [ m; k ] -> (let key = go k in VMap(entries m |> List.filter (fun (k', _) -> compareValue k' key <> 0)))
        | SetAdd, [ s; x ] -> VSet(addElement (items s) (go x))
        | SetRemove, [ s; x ] -> (let key = go x in VSet(items s |> List.filter (fun y -> compareValue y key <> 0)))
        | Keys, [ m ] -> VSet(entries m |> List.map fst)
        | Sorted, [ s ] -> VSeq(items s)
        | Has, [ c; k ] ->
            let key = go k
            match go c with
            | VMap m -> VBool(m |> List.exists (fun (k', _) -> compareValue k' key = 0))
            | VSet s -> VBool(s |> List.exists (fun y -> compareValue y key = 0))
            | _ -> raise (CannotEvaluate "not a map or a set")
        | Get, [ m; k ] ->
            let key = go k
            match entries m |> List.tryFind (fun (k', _) -> compareValue k' key = 0) with
            | Some(_, v) -> v
            | None -> ev.Fail("key in map", e.Span, "key not in map")
        | Union, [ a; b ] -> VSet(items b |> List.fold addElement (items a))
        | Inter, [ a; b ] -> (let sb = items b in VSet(items a |> List.filter (fun x -> sb |> List.exists (fun y -> compareValue x y = 0))))
        | Diff, [ a; b ] -> (let sb = items b in VSet(items a |> List.filter (fun x -> not (sb |> List.exists (fun y -> compareValue x y = 0)))))
        | Subset, [ a; b ] -> (let sb = items b in VBool(items a |> List.forall (fun x -> sb |> List.exists (fun y -> compareValue x y = 0))))
        | _ -> raise (CannotEvaluate "an operation on a map or a set that does not fit")

    /// Does this boolean expression hold? None when it cannot be computed.
    member ev.Holds(e: TExpr, env: Map<string, Value>) : bool option =
        try
            match ev.Expr(e, env) with
            | VBool b -> Some b
            | _ -> None
        with CannotEvaluate _ -> None

    /// A property checked while running: false is a broken obligation; not computable stops the run.
    member private ev.Require(e: TExpr, env: Map<string, Value>, label: string, span: Quod.Syntax.Span) =
        match ev.Holds(e, env) with
        | Some true -> ()
        | Some false -> raise (Violation(label, span))
        | None -> raise (CannotEvaluate("cannot evaluate: " + label))

    member private ev.Int(e: TExpr, env: Map<string, Value>) : BigInteger =
        match ev.Expr(e, env) with
        | VInt n -> n
        | _ -> raise (CannotEvaluate "not an int")

    /// Run a block; the variables it declares end with it, the assignments it makes stay.
    member private ev.Block(items: TStmt list, env: Map<string, Value>) : Map<string, Value> =
        let after = items |> List.fold (fun en s -> ev.Stmt(s, en)) env
        env |> Map.map (fun name _ -> after.[name])

    member private ev.Stmt(s: TStmt, env: Map<string, Value>) : Map<string, Value> =
        steps <- steps + 1
        if steps > 1000000 then raise (CannotEvaluate "too many steps")
        match s.Kind with
        | SLet(_, name, _, value) | SAssign(name, value) -> env.Add(name, ev.Expr(value, env))
        | SAssert e ->
            ev.Require(e, env, "assertion", s.Span)
            env
        | SReturn e -> raise (Returned(ev.Expr(e, env), s.Span))
        | SIf(c, a, b) ->
            match ev.Expr(c, env) with
            | VBool v ->
                taken.Add((s.Span, v)) |> ignore
                ev.Block((if v then a else b), env)
            | _ -> raise (CannotEvaluate "not a bool")
        | SWhile(cond, invs, dec, body) ->
            let numbered = List.zip invs [ 1 .. invs.Length ]
            for (inv, k) in numbered do
                ev.Require(inv, env, "invariant #" + string k + " `" + Printer.exprText (toSyntax inv) + "` holds on entry to the loop", inv.Span)
            let mutable en = env
            let test () =
                match ev.Expr(cond, en) with
                | VBool b -> b
                | _ -> raise (CannotEvaluate "not a bool")
            while test () do
                let m0 = ev.Int(dec, en)
                if m0.Sign < 0 then raise (Violation("loop measure (decreases) is >= 0", dec.Span))
                en <- ev.Block(body, en)
                for (inv, k) in numbered do
                    ev.Require(inv, en, "invariant #" + string k + " `" + Printer.exprText (toSyntax inv) + "` is preserved by the loop body", inv.Span)
                if not (ev.Int(dec, en) < m0) then raise (Violation("loop measure (decreases) gets smaller", dec.Span))
            en

    /// Run a function on arguments (in checking mode: every obligation of its body is checked on
    /// the way, and its postconditions at the return). Its requires are the caller's business.
    member ev.Run(f: TFn, args: Value list) : Value =
        depth <- depth + 1
        let mutable pushed = false
        try
            if depth > maxDepth then raise (CannotEvaluate "recursion too deep")
            let env = List.zip (f.Params |> List.map (fun p -> p.Name)) args |> Map.ofList
            if checking then
                let measure =
                    match f.Decreases with
                    | Some d -> (match ev.Expr(d, env) with VInt m -> Some m | _ -> None)
                    | None -> None
                running <- (f, measure) :: running
                pushed <- true
            let result, span =
                match f.Body with
                | TExprBody body -> ev.Expr(body, env), body.Span
                | TStmtBody items ->
                    try
                        items |> List.fold (fun en s -> ev.Stmt(s, en)) env |> ignore
                        raise (CannotEvaluate "no return")
                    with Returned(v, span) -> v, span
            if checking then
                checkedResult <- Some result
                for (ens, k) in List.zip f.Ensures [ 1 .. f.Ensures.Length ] do
                    ev.Require(ens, env.Add("result", result), "postcondition (ensures #" + string k + ")", span)
            result
        finally
            if pushed then running <- running.Tail
            depth <- depth - 1

    /// Steps taken so far (statements run); reset to bound one run.
    member _.ResetSteps() = steps <- 0