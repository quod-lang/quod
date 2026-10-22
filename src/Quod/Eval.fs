/// Evaluates Quod expressions on concrete values. Used to *confirm* what the solver proposes
/// (a completeness witness, a counterexample) without trusting the solver: contracts are always
/// computable, since quantifiers are bounded and the functions they call are expression
/// functions, which terminate (that is proved before they are used).
module Quod.Eval

open System.Numerics
open Quod.Typed

type Value =
    | VInt of BigInteger
    | VBool of bool
    | VSeq of Value list
    | VTuple of Value list

/// Raised when a value cannot be computed: an index out of bounds, a division by zero, a call
/// to a statement function, a quantifier over a huge range. The caller then confirms nothing.
exception CannotEvaluate of string

/// Bounded quantifiers over more values than this are not evaluated.
let private maxRange = BigInteger 100000

/// Euclidean division, as in SMT-LIB and in the Quod semantics: the remainder is >= 0.
let euclidDivMod (a: BigInteger) (b: BigInteger) =
    let q0 = BigInteger.Divide(a, b)
    let r0 = a - q0 * b
    if r0.Sign < 0 then
        if b.Sign > 0 then q0 - BigInteger.One, r0 + b else q0 + BigInteger.One, r0 - b
    else q0, r0

let rec valueText (v: Value) =
    match v with
    | VInt n -> n.ToString()
    | VBool b -> if b then "true" else "false"
    | VSeq xs -> "[" + (xs |> List.map valueText |> String.concat ", ") + "]"
    | VTuple xs -> "(" + (xs |> List.map valueText |> String.concat ", ") + ")"

type Evaluator(fns: Map<string, TFn>) =
    let mutable depth = 0

    member ev.Expr(e: TExpr, env: Map<string, Value>) : Value =
        let go x = ev.Expr(x, env)
        let asInt x = match go x with VInt n -> n | _ -> raise (CannotEvaluate "not an int")
        let asBool x = match go x with VBool b -> b | _ -> raise (CannotEvaluate "not a bool")
        let asSeq x = match go x with VSeq s -> s | _ -> raise (CannotEvaluate "not a sequence")
        match e.Kind with
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
            if k.Sign < 0 || k >= BigInteger xs.Length then raise (CannotEvaluate "index out of bounds")
            xs.[int k]
        | ESlice(s, lo, hi) ->
            let xs = asSeq s
            let l = lo |> Option.map asInt |> Option.defaultValue BigInteger.Zero
            let h = hi |> Option.map asInt |> Option.defaultValue (BigInteger xs.Length)
            if l.Sign < 0 || l > h || h > BigInteger xs.Length then raise (CannotEvaluate "slice out of bounds")
            VSeq(xs |> List.skip (int l) |> List.take (int (h - l)))
        | EProj(t, k) ->
            match go t with
            | VTuple xs -> xs.[k]
            | _ -> raise (CannotEvaluate "not a tuple")
        | ELen s -> VInt(BigInteger (asSeq s).Length)
        | ECall(name, args) ->
            let f = fns.[name]
            match f.Body with
            | TStmtBody _ -> raise (CannotEvaluate("'" + name + "' is a statement function"))
            | TExprBody body ->
                depth <- depth + 1
                if depth > 10000 then raise (CannotEvaluate "recursion too deep")
                let callEnv = List.zip (f.Params |> List.map (fun p -> p.Name)) (args |> List.map go) |> Map.ofList
                let r = ev.Expr(body, callEnv)
                depth <- depth - 1
                r
        | ENeg x -> VInt(-(asInt x))
        | ENot x -> VBool(not (asBool x))
        | EArith(op, a, b) ->
            let x, y = asInt a, asInt b
            match op with
            | OAdd -> VInt(x + y)
            | OSub -> VInt(x - y)
            | OMul -> VInt(x * y)
            | ODiv | OMod ->
                if y.IsZero then raise (CannotEvaluate "division by zero")
                let q, r = euclidDivMod x y
                VInt(if op = ODiv then q else r)
        | EConcat(a, b) -> VSeq(asSeq a @ asSeq b)
        | ECmp(op, a, b) ->
            let x, y = asInt a, asInt b
            VBool(match op with OLt -> x < y | OLe -> x <= y | OGt -> x > y | OGe -> x >= y)
        | EEq(a, b) -> VBool(go a = go b)
        | ELogic(op, a, b) ->
            match op with
            | OAnd -> VBool(asBool a && asBool b) // && and || short-circuit, as guards do in proofs
            | OOr -> VBool(asBool a || asBool b)
            | OImplies -> VBool(not (asBool a) || asBool b)
            | OIff -> VBool(asBool a = asBool b)
        | EIf(c, a, b) -> if asBool c then go a else go b
        | EQuant(q, name, lo, hi, body) ->
            let l, h = asInt lo, asInt hi
            if h - l > maxRange then raise (CannotEvaluate "quantifier range too large")
            let values = if h <= l then Seq.empty else seq { for i in 0 .. int (h - l) - 1 -> l + BigInteger i }
            let test (i: BigInteger) = match ev.Expr(body, env.Add(name, VInt i)) with VBool b -> b | _ -> false
            match q with
            | Syntax.Forall -> VBool(Seq.forall test values)
            | Syntax.Exists -> VBool(Seq.exists test values)
        | EToNat x -> go x

    /// Is the value of the expected type (a nat is >= 0, recursively)?
    member ev.Fits(t: Ty, v: Value) : bool =
        match t, v with
        | TyNat, VInt n -> n.Sign >= 0
        | TyInt, VInt _ -> true
        | TyBool, VBool _ -> true
        | TySeq e, VSeq xs -> xs |> List.forall (fun x -> ev.Fits(e, x))
        | TyTuple ts, VTuple xs when ts.Length = xs.Length -> List.forall2 (fun t x -> ev.Fits(t, x)) ts xs
        | _ -> false

    /// Does this boolean expression hold? None when it cannot be computed.
    member ev.Holds(e: TExpr, env: Map<string, Value>) : bool option =
        try
            match ev.Expr(e, env) with
            | VBool b -> Some b
            | _ -> None
        with CannotEvaluate _ -> None
