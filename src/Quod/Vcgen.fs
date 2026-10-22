/// Verification of Quod 0.1 functions by symbolic execution over the typed representation.
///
/// Each function is walked with a *state*: the facts known on the current path (assumptions) and
/// the current SMT term of every variable (each assignment makes a new version, x@1, x@2...).
/// Every place that can go wrong raises an *obligation*, checked on its own by asking Z3 whether
/// the assumptions together with the negated obligation are satisfiable: unsat means proved; sat
/// gives a model, turned into a counterexample on the parameters. A checked obligation is then
/// assumed, so that one failure does not cascade into others.
module Quod.Vcgen

open System
open System.Collections.Generic
open Quod.Syntax
open Quod.Typed
open Quod.Smt
open Quod.Diagnostics

// --- sorts and names ------------------------------------------------------------------

/// nat and int share the SMT sort Int: a nat is an Int with a `>= 0` fact.
let rec private tySig (t: Ty) =
    match t with
    | TyInt | TyNat | TyError -> "i"
    | TyBool -> "b"
    | TySeq e -> "S" + tySig e + "E"
    | TyTuple ts -> "T" + (ts |> List.map tySig |> String.concat "") + "E"

let private tupleName (ts: Ty list) = "Tup_" + (ts |> List.map tySig |> String.concat "")

let rec sortOf (t: Ty) =
    match t with
    | TyInt | TyNat | TyError -> "Int"
    | TyBool -> "Bool"
    | TySeq e -> "(Seq " + sortOf e + ")"
    | TyTuple ts -> tupleName ts

let private fnSym (name: string) = "f_" + name

let private app (f: string) (args: string list) =
    if args.IsEmpty then f else "(" + f + " " + String.Join(" ", args) + ")"

let private conj (terms: string list) =
    match terms with
    | [] -> "true"
    | [ t ] -> t
    | ts -> "(and " + String.Join(" ", ts) + ")"

let private implies (guards: string list) (goal: string) =
    if guards.IsEmpty then goal else "(=> " + conj (List.rev guards) + " " + goal + ")"

let private intLit (v: bigint) = if v.Sign < 0 then "(- " + (-v).ToString() + ")" else v.ToString()

/// Facts that a value of type t carries: a nat is >= 0, and so are the elements of a seq<nat>.
let rec private typeFacts (fresh: unit -> string) (t: Ty) (term: string) : string list =
    match t with
    | TyNat -> [ "(>= " + term + " 0)" ]
    | TySeq e ->
        let q = fresh ()
        match typeFacts fresh e ("(seq.nth " + term + " " + q + ")") with
        | [] -> []
        | fs -> [ "(forall ((" + q + " Int)) (=> (and (<= 0 " + q + ") (< " + q + " (seq.len " + term + "))) " + conj fs + "))" ]
    | TyTuple ts ->
        ts |> List.mapi (fun k ct -> typeFacts fresh ct ("(" + tupleName ts + "_" + string k + " " + term + ")")) |> List.concat
    | _ -> []

// --- obligations ----------------------------------------------------------------------

type private Obligation = { Goal: string; Label: string; Span: Span }

/// What translating an expression produces besides its term: obligations (each already closed
/// under the guards of its position) and facts (valid implications, e.g. callee contracts).
type private Collector() =
    member val Obs = ResizeArray<Obligation>()
    member val Facts = ResizeArray<string>()

type private FnInfo =
    { Fn: TFn
      InitialMeasure: string option
      /// false when the termination of this function was already checked (see verify)
      CheckDecreases: bool }

type private State = { Env: Map<string, string>; Assume: string list; Alive: bool }

/// A Z3 model value printed as a Quod value: numbers, booleans, sequences, tuples.
let rec private renderValue (e: SExpr) : string =
    let rec items (x: SExpr) : string list option =
        match x with
        | List [ Atom "as"; Atom "seq.empty"; _ ] -> Some []
        | List [ Atom "seq.unit"; y ] -> Some [ renderValue y ]
        | List(Atom "seq.++" :: parts) ->
            parts |> List.map items |> List.fold (fun acc p -> Option.map2 (@) acc p) (Some [])
        | _ -> None
    match e with
    | Atom a -> a
    | List [ Atom "-"; Atom n ] -> "-" + n
    | List(Atom ctor :: args) when ctor.StartsWith "mk_Tup_" -> "(" + (args |> List.map renderValue |> String.concat ", ") + ")"
    | other ->
        match items other with
        | Some xs -> "[" + String.concat ", " xs + "]"
        | None -> sexprText other

/// Variables assigned anywhere in a loop body (the ones a loop must forget).
/// A Z3 model value as a concrete Quod value, for the evaluator (None if not understood).
let rec private valueOf (t: Ty) (e: SExpr) : Eval.Value option =
    let rec seqItems (elem: Ty) (x: SExpr) : Eval.Value list option =
        match x with
        | List [ Atom "as"; Atom "seq.empty"; _ ] -> Some []
        | List [ Atom "seq.unit"; y ] -> valueOf elem y |> Option.map (fun v -> [ v ])
        | List(Atom "seq.++" :: parts) ->
            parts |> List.map (seqItems elem) |> List.fold (fun acc p -> Option.map2 (@) acc p) (Some [])
        | _ -> None
    match t, e with
    | (TyInt | TyNat), Atom n ->
        match bigint.TryParse n with
        | true, v -> Some(Eval.VInt v)
        | _ -> None
    | (TyInt | TyNat), List [ Atom "-"; Atom n ] ->
        match bigint.TryParse n with
        | true, v -> Some(Eval.VInt(-v))
        | _ -> None
    | TyBool, Atom "true" -> Some(Eval.VBool true)
    | TyBool, Atom "false" -> Some(Eval.VBool false)
    | TySeq elem, x -> seqItems elem x |> Option.map Eval.VSeq
    | TyTuple ts, List(Atom _ :: args) when args.Length = ts.Length ->
        let parts = List.map2 valueOf ts args
        if parts |> List.forall Option.isSome then Some(Eval.VTuple(parts |> List.map Option.get)) else None
    | _ -> None

let rec private assignedIn (body: TStmt list) : string list =
    body |> List.collect (fun s ->
        match s.Kind with
        | SAssign(n, _) -> [ n ]
        | SIf(_, a, b) -> assignedIn a @ assignedIn b
        | SWhile(_, _, _, b) -> assignedIn b
        | _ -> [])

// --- the verifier ---------------------------------------------------------------------

type private Verifier(file: string, prog: TProgram, z3: Session) =
    let fns = prog.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList
    let diags = ResizeArray<Diagnostic>()
    let mutable counter = 0
    let mutable proved = 0
    let mutable current: FnInfo option = None
    let paramsOf = Dictionary<string, (string * Ty) list>()

    member _.Diagnostics = List.ofSeq diags
    member _.Proved = proved

    member _.Fresh(prefix: string) =
        counter <- counter + 1
        prefix + "@" + string counter

    member v.FreshQ() = v.Fresh "q"

    /// Declare a new SMT constant of type t and return its name.
    member v.Const(baseName: string, t: Ty) : string =
        let name = v.Fresh baseName
        z3.Send("(declare-const " + name + " " + sortOf t + ")")
        name

    // --- expressions ------------------------------------------------------------------

    member v.Expr(e: TExpr, env: Map<string, string>, guards: string list, out: Collector) : string =
        let go x = v.Expr(x, env, guards, out)
        let ob (goal: string) (label: string) (span: Span) =
            out.Obs.Add { Goal = implies guards goal; Label = label; Span = span }
        match e.Kind with
        | EInt n -> intLit n
        | EBool b -> if b then "true" else "false"
        | EVar n ->
            match env.TryFind n with
            | Some t -> t
            | None -> failwith ("internal: unbound variable " + n)
        | EResult -> env.["result"]
        | ESeq [] -> "(as seq.empty " + sortOf e.Ty + ")"
        | ESeq [ x ] -> "(seq.unit " + go x + ")"
        | ESeq xs -> "(seq.++ " + String.Join(" ", xs |> List.map (fun x -> "(seq.unit " + go x + ")")) + ")"
        | ETuple xs -> app ("mk_" + tupleName (xs |> List.map (fun x -> x.Ty))) (xs |> List.map go)
        | EIndex(s, i) ->
            let ts, ti = go s, go i
            ob ("(and (<= 0 " + ti + ") (< " + ti + " (seq.len " + ts + ")))") "index in bounds" e.Span
            "(seq.nth " + ts + " " + ti + ")"
        | ESlice(s, lo, hi) ->
            let ts = go s
            let tlo = lo |> Option.map go |> Option.defaultValue "0"
            let thi = hi |> Option.map go |> Option.defaultValue ("(seq.len " + ts + ")")
            ob ("(and (<= 0 " + tlo + ") (<= " + tlo + " " + thi + ") (<= " + thi + " (seq.len " + ts + ")))")
                "slice bounds (0 <= lo <= hi <= len)" e.Span
            "(seq.extract " + ts + " " + tlo + " (- " + thi + " " + tlo + "))"
        | EProj(t, k) ->
            match t.Ty with
            | TyTuple ts -> "(" + tupleName ts + "_" + string k + " " + go t + ")"
            | _ -> failwith "internal: projection of a non-tuple"
        | ELen s -> "(seq.len " + go s + ")"
        | ECall(name, args) -> v.Call(e, name, args |> List.map go, guards, out)
        | ENeg x -> "(- " + go x + ")"
        | ENot x -> "(not " + go x + ")"
        | EArith(op, a, b) ->
            let ta, tb = go a, go b
            match op with
            | OAdd -> "(+ " + ta + " " + tb + ")"
            | OSub -> "(- " + ta + " " + tb + ")"
            | OMul -> "(* " + ta + " " + tb + ")"
            | ODiv | OMod ->
                ob ("(not (= " + tb + " 0))") "divisor is not zero" b.Span
                (if op = ODiv then "(div " else "(mod ") + ta + " " + tb + ")"
        | EConcat(a, b) -> "(seq.++ " + go a + " " + go b + ")"
        | ECmp(op, a, b) ->
            let o = match op with OLt -> "<" | OLe -> "<=" | OGt -> ">" | OGe -> ">="
            "(" + o + " " + go a + " " + go b + ")"
        | EEq(a, b) -> "(= " + go a + " " + go b + ")"
        | ELogic(op, a, b) ->
            let ta = go a
            match op with
            | OAnd -> "(and " + ta + " " + v.Expr(b, env, ta :: guards, out) + ")"
            | OOr -> "(or " + ta + " " + v.Expr(b, env, ("(not " + ta + ")") :: guards, out) + ")"
            | OImplies -> "(=> " + ta + " " + v.Expr(b, env, ta :: guards, out) + ")"
            | OIff -> "(= " + ta + " " + go b + ")"
        | EIf(c, a, b) ->
            let tc = go c
            let ta = v.Expr(a, env, tc :: guards, out)
            let tb = v.Expr(b, env, ("(not " + tc + ")") :: guards, out)
            "(ite " + tc + " " + ta + " " + tb + ")"
        | EQuant(q, name, lo, hi, body) ->
            let tlo, thi = go lo, go hi
            let sym = v.FreshQ()
            let range = "(and (<= " + tlo + " " + sym + ") (< " + sym + " " + thi + "))"
            let inner = Collector()
            let tbody = v.Expr(body, env.Add(name, sym), range :: guards, inner)
            // Obligations and facts found under the quantifier hold for every value in range.
            for o in inner.Obs do
                out.Obs.Add { o with Goal = "(forall ((" + sym + " Int)) " + o.Goal + ")" }
            for f in inner.Facts do
                out.Facts.Add("(forall ((" + sym + " Int)) " + f + ")")
            match q with
            | Forall -> "(forall ((" + sym + " Int)) (=> " + range + " " + tbody + "))"
            | Exists -> "(exists ((" + sym + " Int)) (and " + range + " " + tbody + "))"
        | EToNat x ->
            let tx = go x
            ob ("(>= " + tx + " 0)") "value is a nat (>= 0)" e.Span
            tx

    /// A call: the callee's precondition is an obligation; its contract is a fact; a call
    /// inside the same recursive cycle must make the measure smaller.
    member v.Call(e: TExpr, name: string, args: string list, guards: string list, out: Collector) : string =
        let callee = fns.[name]
        let term = app (fnSym name) args
        let calleeEnv = List.zip (callee.Params |> List.map (fun p -> p.Name)) args |> Map.ofList
        let silent = Collector() // the callee's contract is well-formed: proved when it was checked
        let reqs = callee.Requires |> List.map (fun r -> v.Expr(r, calleeEnv, [], silent))
        for (r, k) in List.zip reqs [ 1 .. reqs.Length ] do
            out.Obs.Add
                { Goal = implies guards r
                  Label = "precondition of '" + name + "'" + (if reqs.Length > 1 then " (requires #" + string k + ")" else "")
                  Span = e.Span }
        let ens = callee.Ensures |> List.map (fun x -> v.Expr(x, calleeEnv.Add("result", term), [], silent))
        let retFacts = typeFacts v.FreshQ callee.Ret term
        // The contract holds only when the arguments fit the parameter types (a nat argument
        // is >= 0) as well as the requires: f(n - 1) says nothing when n - 1 is negative.
        let argFacts = List.zip callee.Params args |> List.collect (fun (p, a) -> typeFacts v.FreshQ p.Ty a)
        out.Facts.Add("(=> " + conj (argFacts @ reqs) + " " + conj (ens @ retFacts) + ")")
        for f in silent.Facts do
            out.Facts.Add f
        match current with
        | Some info when info.CheckDecreases && info.Fn.IsRecursive && callee.Cycle = info.Fn.Cycle ->
            match info.InitialMeasure, callee.Decreases with
            | Some m0, Some d ->
                let m1 = v.Expr(d, calleeEnv, [], silent)
                out.Obs.Add
                    { Goal = implies guards ("(and (<= 0 " + m0 + ") (< " + m1 + " " + m0 + "))")
                      Label = "recursive call decreases the measure (and it stays >= 0)"
                      Span = e.Span }
            | _ -> () // missing decreases: already a type error
        | _ -> ()
        term

    // --- checking -----------------------------------------------------------------------

    /// Check one obligation on the current path, report it if it fails, then assume it.
    member v.Check(st: State, o: Obligation) : State =
        z3.Push()
        for a in List.rev st.Assume do
            z3.Send("(assert " + a + ")")
        z3.Send("(assert (not " + o.Goal + "))")
        match z3.Check() with
        | Unsat -> proved <- proved + 1
        | Sat -> v.Report(o, "refuted", "cannot prove: " + o.Label, v.Counterexample())
        | Unknown "timeout" ->
            v.Report(o, "inconclusive", "could not prove " + o.Label + " within the time limit", [])
        | Unknown _ ->
            // Quantifiers make Z3 incomplete: it stops with a candidate model it cannot confirm.
            // Shown as a *possible* counterexample: it often is the real one.
            match v.Counterexample() with
            | [] -> v.Report(o, "inconclusive", "could not prove " + o.Label, [])
            | cex -> v.Report(o, "inconclusive", "cannot prove: " + o.Label + " (possible counterexample, not confirmed by the solver)", cex)
        z3.Pop()
        { st with Assume = o.Goal :: st.Assume }

    /// The parameters' values in the current model (empty when there is none).
    member v.Counterexample() : (string * string) list =
        let ps = paramsOf.[current.Value.Fn.Name]
        let values = z3.Values(ps |> List.map fst)
        if values.Length <> ps.Length then []
        else List.zip ps values |> List.map (fun ((sym, _), value) -> (sym.Substring(0, sym.IndexOf '@'), renderValue value))

    member v.Report(o: Obligation, status: string, message: string, cex: (string * string) list) =
        diags.Add
            { File = file; Span = o.Span; Kind = "proof"; Status = status; Severity = Error
              Fn = Some current.Value.Fn.Name; Property = Some o.Label; Counterexample = cex; Message = message }

    /// Translate e on the current path: check its obligations, assume its facts.
    member v.Eval(st: State, e: TExpr) : State * string =
        let out = Collector()
        let term = v.Expr(e, st.Env, [], out)
        let mutable s = { st with Assume = List.rev (List.ofSeq out.Facts) @ st.Assume }
        for o in out.Obs do
            s <- v.Check(s, o)
        s, term

    /// Prove a boolean property (an assertion, an invariant, a postcondition) on the path.
    member v.Prove(st: State, e: TExpr, label: string, span: Span) : State =
        let s, term = v.Eval(st, e)
        v.Check(s, { Goal = term; Label = label; Span = span })

    member v.Assume(st: State, e: TExpr) : State =
        let s, term = v.Eval(st, e)
        { s with Assume = term :: s.Assume }

    member v.Ensures(st: State, f: TFn, resultTerm: string, span: Span) =
        let mutable s = { st with Env = st.Env.Add("result", resultTerm) }
        for (ens, k) in List.zip f.Ensures [ 1 .. f.Ensures.Length ] do
            s <- v.Prove(s, ens, "postcondition (ensures #" + string k + ")", span)

    // --- statements ---------------------------------------------------------------------

    member v.Stmts(st: State, items: TStmt list, f: TFn, types: Dictionary<string, Ty>) : State =
        items |> List.fold (fun s item -> if s.Alive then v.Stmt(s, item, f, types) else s) st

    member v.Bind(st: State, name: string, t: Ty, term: string, types: Dictionary<string, Ty>) : State =
        let c = v.Const(name, t)
        types.[name] <- t
        { st with
            Env = st.Env.Add(name, c)
            Assume = (typeFacts v.FreshQ t c |> List.rev) @ (("(= " + c + " " + term + ")") :: st.Assume) }

    member v.Stmt(st: State, s: TStmt, f: TFn, types: Dictionary<string, Ty>) : State =
        match s.Kind with
        | SLet(_, name, t, value) ->
            let st, term = v.Eval(st, value)
            v.Bind(st, name, t, term, types)
        | SAssign(name, value) ->
            let st, term = v.Eval(st, value)
            v.Bind(st, name, types.[name], term, types)
        | SAssert e -> v.Prove(st, e, "assertion", s.Span)
        | SReturn e ->
            let st, term = v.Eval(st, e)
            v.Ensures(st, f, term, s.Span)
            { st with Alive = false }
        | SIf(c, thenB, elseB) ->
            let st, tc = v.Eval(st, c)
            let thenS = v.Stmts({ st with Assume = tc :: st.Assume }, thenB, f, types)
            let elseS = v.Stmts({ st with Assume = ("(not " + tc + ")") :: st.Assume }, elseB, f, types)
            v.Merge(st, tc, thenS, elseS, types)
        | SWhile(cond, invs, dec, body) -> v.Loop(st, s, cond, invs, dec, body, f, types)

    /// Join the two branches of an if: variables that differ get a new version defined by ite.
    member v.Merge(st: State, tc: string, a: State, b: State, types: Dictionary<string, Ty>) : State =
        match a.Alive, b.Alive with
        | false, false -> { st with Alive = false }
        | true, false -> { a with Env = st.Env |> Map.map (fun k _ -> a.Env.[k]) }
        | false, true -> { b with Env = st.Env |> Map.map (fun k _ -> b.Env.[k]) }
        | true, true ->
            let extra (x: State) = List.take (x.Assume.Length - st.Assume.Length) x.Assume
            let mutable assume =
                ("(=> (not " + tc + ") " + conj (extra b) + ")") :: ("(=> " + tc + " " + conj (extra a) + ")") :: st.Assume
            let mutable env = st.Env
            for KeyValue(name, _) in st.Env do
                let ta, tb = a.Env.[name], b.Env.[name]
                if ta <> tb then
                    let c = v.Const(name, types.[name])
                    assume <- ("(= " + c + " (ite " + tc + " " + ta + " " + tb + "))") :: assume
                    env <- env.Add(name, c)
            { Env = env; Assume = assume; Alive = true }

    /// A loop is replaced by its invariants: prove them on entry; forget (havoc) the variables
    /// the body assigns; prove that one arbitrary iteration preserves them and decreases the
    /// measure; continue after the loop knowing the invariants and the negated condition.
    member v.Loop(st: State, s: TStmt, cond: TExpr, invs: TExpr list, dec: TExpr, body: TStmt list,
                  f: TFn, types: Dictionary<string, Ty>) : State =
        let numbered = List.zip invs [ 1 .. invs.Length ]
        let mutable entry = st
        for (inv, k) in numbered do
            entry <- v.Prove(entry, inv, "invariant #" + string k + " holds on entry to the loop", inv.Span)
        let modified = assignedIn body |> List.filter st.Env.ContainsKey |> List.distinct
        let mutable loop = entry
        for name in modified do
            let c = v.Const(name, types.[name])
            loop <- { loop with Env = loop.Env.Add(name, c); Assume = (typeFacts v.FreshQ types.[name] c |> List.rev) @ loop.Assume }
        for (inv, _) in numbered do
            loop <- v.Assume(loop, inv)
        // one arbitrary iteration
        let iter0, tc = v.Eval(loop, cond)
        let iter1 = { iter0 with Assume = tc :: iter0.Assume }
        let iter2, m0 = v.Eval(iter1, dec)
        let iter3 = v.Check(iter2, { Goal = "(>= " + m0 + " 0)"; Label = "loop measure (decreases) is >= 0"; Span = dec.Span })
        let finish = v.Stmts(iter3, body, f, types)
        if finish.Alive then
            let mutable e = finish
            for (inv, k) in numbered do
                e <- v.Prove(e, inv, "invariant #" + string k + " is preserved by the loop body", inv.Span)
            let e2, m1 = v.Eval(e, dec)
            v.Check(e2, { Goal = "(< " + m1 + " " + m0 + ")"; Label = "loop measure (decreases) gets smaller"; Span = dec.Span }) |> ignore
        // after the loop
        let afterS, tc2 = v.Eval(loop, cond)
        { afterS with Assume = ("(not " + tc2 + ")") :: afterS.Assume }

    // --- functions ----------------------------------------------------------------------

    member v.Function(f: TFn) =
        z3.Push()
        let types = Dictionary<string, Ty>()
        let mutable st = { Env = Map.empty; Assume = []; Alive = true }
        let ps = ResizeArray<string * Ty>()
        for p in f.Params do
            let c = v.Const(p.Name, p.Ty)
            types.[p.Name] <- p.Ty
            ps.Add(c, p.Ty)
            st <- { st with Env = st.Env.Add(p.Name, c); Assume = (typeFacts v.FreshQ p.Ty c |> List.rev) @ st.Assume }
        paramsOf.[f.Name] <- List.ofSeq ps
        let checkDec = not (f.IsExprFn && f.IsRecursive) // expression functions: checked by Termination
        current <- Some { Fn = f; InitialMeasure = None; CheckDecreases = checkDec }
        for r in f.Requires do
            st <- v.Assume(st, r) // its own obligations (well-formedness) are checked by Eval
        // Under an impossible precondition everything is "proved": reject it explicitly, or a
        // `requires false` would make any function verify (and look complete).
        if not f.Requires.IsEmpty then
            z3.Push()
            for a in List.rev st.Assume do
                z3.Send("(assert " + a + ")")
            // A contradiction is found fast; finding a model of quantified requires can take
            // long and proves nothing either way, so this check gets a short time limit.
            z3.SetTimeout(min 1000 z3.DefaultTimeout)
            let answer = z3.Check()
            z3.SetTimeout z3.DefaultTimeout
            match answer with
            | Unsat ->
                diags.Add
                    { File = file; Span = f.Span; Kind = "proof"; Status = "error"; Severity = Error
                      Fn = Some f.Name; Property = Some "precondition is satisfiable"; Counterexample = []
                      Message = "the 'requires' clauses can never all hold, so this function could never be called and every proof about it would be empty" }
            | _ -> ()
            z3.Pop()
        let measure =
            f.Decreases |> Option.map (fun d ->
                let s2, m = v.Eval(st, d)
                st <- s2
                m)
        current <- Some { Fn = f; InitialMeasure = measure; CheckDecreases = checkDec }
        match f.Body with
        | TExprBody e ->
            let s2, term = v.Eval(st, e)
            v.Ensures(s2, f, term, e.Span)
        | TStmtBody items -> v.Stmts(st, items, f, types) |> ignore
        current <- None
        z3.Pop()

    /// Declarations shared by all functions: tuple datatypes, statement functions (known by
    /// their contract only), and expression functions (known by their definition).
    member v.Prelude() =
        let tuples = ResizeArray<Ty list>()
        let rec visit (t: Ty) =
            match t with
            | TySeq e -> visit e
            | TyTuple ts ->
                List.iter visit ts
                let key = ts |> List.map tySig
                if not (tuples |> Seq.exists (fun x -> (x |> List.map tySig) = key)) then tuples.Add ts
            | _ -> ()
        let rec visitE (e: TExpr) =
            visit e.Ty
            match e.Kind with
            | ESeq xs | ETuple xs | ECall(_, xs) -> List.iter visitE xs
            | EIndex(a, b) | EArith(_, a, b) | EConcat(a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> visitE a; visitE b
            | ESlice(a, b, c) -> visitE a; Option.iter visitE b; Option.iter visitE c
            | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a -> visitE a
            | EIf(a, b, c) | EQuant(_, _, a, b, c) -> visitE a; visitE b; visitE c
            | _ -> ()
        let rec visitS (s: TStmt) =
            match s.Kind with
            | SLet(_, _, t, e) -> visit t; visitE e
            | SAssign(_, e) | SAssert e | SReturn e -> visitE e
            | SIf(c, a, b) -> visitE c; List.iter visitS a; List.iter visitS b
            | SWhile(c, invs, d, b) -> visitE c; List.iter visitE invs; visitE d; List.iter visitS b
        for f in prog.Fns do
            visit f.Ret
            for p in f.Params do visit p.Ty
            f.Requires @ f.Ensures @ Option.toList f.Decreases |> List.iter visitE
            match f.Body with
            | TExprBody e -> visitE e
            | TStmtBody ss -> List.iter visitS ss
        for ts in tuples do
            let n = tupleName ts
            let fields = ts |> List.mapi (fun k t -> "(" + n + "_" + string k + " " + sortOf t + ")") |> String.concat " "
            z3.Send("(declare-datatypes ((" + n + " 0)) (((mk_" + n + " " + fields + "))))")
        // Every function is an SMT function symbol. A pure function returns the same result for
        // the same arguments, so this is sound even for statement functions, which callers know
        // through their contract only.
        for f in prog.Fns do
            z3.Send("(declare-fun " + fnSym f.Name + " (" + String.Join(" ", f.Params |> List.map (fun p -> sortOf p.Ty)) + ") " + sortOf f.Ret + ")")
    /// An expression function is also known by its definition, as an axiom guarded by its
    /// parameter types and requires, and triggered only when a call f(...) appears (as Dafny
    /// does). Z3's define-funs-rec unfolds recursive definitions eagerly and times out on simple
    /// facts (a factorial is >= 0); the triggered axiom answers in milliseconds. Only added for
    /// functions known to terminate: `f(xs) = xs[0] + f(xs)` would be a contradiction that
    /// makes every later proof vacuous.
    member v.Define(f: TFn) =
        let env = f.Params |> List.map (fun p -> p.Name, "p_" + p.Name) |> Map.ofList
        let body =
            match f.Body with
            | TExprBody e -> v.Expr(e, env, [], Collector())
            | TStmtBody _ -> failwith "internal"
        let silent = Collector()
        let guards =
            (f.Params |> List.collect (fun p -> typeFacts v.FreshQ p.Ty ("p_" + p.Name)))
            @ (f.Requires |> List.map (fun r -> v.Expr(r, env, [], silent)))
        let call = app (fnSym f.Name) (f.Params |> List.map (fun p -> "p_" + p.Name))
        let definition = "(=> " + conj guards + " (= " + call + " " + body + "))"
        if f.Params.IsEmpty then
            z3.Send("(assert " + definition + ")")
        else
            let binders = String.Join(" ", f.Params |> List.map (fun p -> "(p_" + p.Name + " " + sortOf p.Ty + ")"))
            z3.Send("(assert (forall (" + binders + ") (! " + definition + " :pattern (" + call + "))))")

    /// Check that a recursive expression function terminates, before its definition is known:
    /// only the "recursive call decreases" obligations of its body, under its requires.
    /// Returns true when they all hold.
    member v.Termination(f: TFn) : bool =
        let before = diags.Count
        z3.Push()
        let silent = Collector()
        let mutable env = Map.empty
        let mutable assume = []
        let ps = ResizeArray<string * Ty>()
        for p in f.Params do
            let c = v.Const(p.Name, p.Ty)
            ps.Add(c, p.Ty)
            env <- env.Add(p.Name, c)
            assume <- (typeFacts v.FreshQ p.Ty c |> List.rev) @ assume
        paramsOf.[f.Name] <- List.ofSeq ps
        for r in f.Requires do
            assume <- v.Expr(r, env, [], silent) :: assume
        let measure = f.Decreases |> Option.map (fun d -> v.Expr(d, env, [], silent))
        current <- Some { Fn = f; InitialMeasure = measure; CheckDecreases = true }
        let out = Collector()
        match f.Body with
        | TExprBody e -> v.Expr(e, env, [], out) |> ignore
        | TStmtBody _ -> ()
        let mutable st = { Env = env; Assume = List.rev (List.ofSeq out.Facts) @ List.rev (List.ofSeq silent.Facts) @ assume; Alive = true }
        for o in out.Obs |> Seq.filter (fun o -> o.Label.StartsWith "recursive call decreases") do
            st <- v.Check(st, o)
        current <- None
        z3.Pop()
        diags.Count = before

    /// Completeness (pillar 5): can two different results satisfy the contract for the same
    /// valid input (or, with `loose`, two results that the declared relation does not allow)?
    /// unsat: determined. Otherwise the solver's candidate (input, r1, r2) is *evaluated* on
    /// concrete values: if the contract really accepts both, the function is underspecified
    /// (an error, with a certain witness); if not, the verdict is inconclusive (a warning).
    member v.Completeness(f: TFn) : bool =
        z3.Push()
        let silent = Collector()
        let mutable env = Map.empty
        let mutable assume = []
        let ps = ResizeArray<string * Ty>()
        for p in f.Params do
            let c = v.Const(p.Name, p.Ty)
            ps.Add(c, p.Ty)
            env <- env.Add(p.Name, c)
            assume <- (typeFacts v.FreshQ p.Ty c |> List.rev) @ assume
        paramsOf.[f.Name] <- List.ofSeq ps
        current <- Some { Fn = f; InitialMeasure = None; CheckDecreases = false }
        for r in f.Requires do
            assume <- v.Expr(r, env, [], silent) :: assume
        let r1 = v.Const("result_a", f.Ret)
        let r2 = v.Const("result_b", f.Ret)
        assume <- (typeFacts v.FreshQ f.Ret r1 @ typeFacts v.FreshQ f.Ret r2 |> List.rev) @ assume
        for ens in f.Ensures do
            assume <- v.Expr(ens, env.Add("result", r1), [], silent) :: v.Expr(ens, env.Add("result", r2), [], silent) :: assume
        let goal =
            match f.Loose with
            | Some l -> v.Expr(l.Relation, env.Add(l.Left, r1).Add(l.Right, r2), [], silent)
            | None -> "(= " + r1 + " " + r2 + ")"
        for a in List.rev (List.ofSeq silent.Facts) @ List.rev assume do
            z3.Send("(assert " + a + ")")
        z3.Send("(assert (not " + goal + "))")
        let answer = z3.Check()
        let candidate () =
            let terms = (ps |> Seq.map fst |> List.ofSeq) @ [ r1; r2 ]
            let values = z3.Values terms
            let types = (ps |> Seq.map snd |> List.ofSeq) @ [ f.Ret; f.Ret ]
            if values.Length <> terms.Length then None
            else
                let parsed = List.map2 valueOf types values
                if parsed |> List.forall Option.isSome then Some(parsed |> List.map Option.get) else None
        let report (status: string) (severity: Severity) (message: string) (witness: (string * string) list) =
            diags.Add
                { File = file; Span = f.Span; Kind = "completeness"; Status = status; Severity = severity
                  Fn = Some f.Name; Property = Some "the contract determines a unique result"
                  Counterexample = witness; Message = message }
        /// Evaluate a candidate (inputs, result a, result b) on concrete values: Some witness
        /// when the contract really accepts both results, None otherwise.
        let confirm (values: Eval.Value list) : (string * string) list option =
            let names = f.Params |> List.map (fun p -> p.Name)
            let inputs = List.zip names (List.take names.Length values)
            let a, b = values.[names.Length], values.[names.Length + 1]
            let ev = Eval.Evaluator(fns)
            let inEnv = Map.ofList inputs
            let holds e en = ev.Holds(e, en) = Some true
            let ok =
                List.forall2 (fun (p: TParam) (_, x) -> ev.Fits(p.Ty, x)) f.Params inputs
                && ev.Fits(f.Ret, a) && ev.Fits(f.Ret, b)
                && f.Requires |> List.forall (fun r -> holds r inEnv)
                && f.Ensures |> List.forall (fun e -> holds e (inEnv.Add("result", a)) && holds e (inEnv.Add("result", b)))
                && (match f.Loose with
                    | Some l -> ev.Holds(l.Relation, inEnv.Add(l.Left, a).Add(l.Right, b)) = Some false
                    | None -> a <> b)
            if ok then
                Some((inputs |> List.map (fun (n, x) -> n, Eval.valueText x))
                     @ [ "result_a", Eval.valueText a; "result_b", Eval.valueText b ])
            else None
        let fromCandidate () = candidate () |> Option.bind confirm
        let witness =
            match answer with
            | Unsat -> None
            | _ ->
                match fromCandidate () with
                | Some w -> Some w
                | None ->
                    // The fast mode (no model-based quantifier instantiation) gives approximate
                    // candidates. Ask again with model search on, briefly: it finds exact models
                    // of sat formulas with quantifiers. The evaluator still confirms everything.
                    z3.Send "(set-option :smt.mbqi true)"
                    z3.SetTimeout(min 3000 z3.DefaultTimeout)
                    let second = z3.Check()
                    let w = match second with Unsat -> None | _ -> fromCandidate ()
                    z3.Send "(set-option :smt.mbqi false)"
                    z3.SetTimeout z3.DefaultTimeout
                    w
        let determined =
            match answer, witness with
            | Unsat, _ -> true
            | _, Some w ->
                let message =
                    match f.Loose with
                    | Some l ->
                        "the contract accepts two results that the 'loose' relation does not allow ("
                        + l.Left + " and " + l.Right + " below): strengthen the ensures clauses, or widen 'loose' if that freedom is intended"
                    | None ->
                        "the contract accepts two different results for the same input: add ensures clauses until "
                        + "only the intended result is allowed, or declare the freedom with 'loose'"
                report "underspecified" Error message w
                false
            | Unknown "timeout", None ->
                report "inconclusive" Warning "completeness not decided within the time limit (the contract may well be complete)" []
                false
            | _, None ->
                report "inconclusive" Warning "completeness not decided: no confirmed witness, no uniqueness proof (the contract may well be complete; a lemma may be needed)" []
                false
        current <- None
        z3.Pop()
        determined

type VerifyResult =
    { Diagnostics: Diagnostic list
      Proved: int
      /// Functions whose contract was proved to determine a unique result (or its loose relation)
      Determined: int
      /// Functions with at least one ensures clause (the ones the completeness check applies to)
      WithContract: int }

/// Verify every function of a well-typed program with one Z3 session:
/// 1. declarations; definitions of the non-recursive expression functions;
/// 2. termination of the recursive expression functions, without their definitions;
/// 3. definitions of those that terminate;
/// 4. every function, with all the definitions that are safe to know.
let verify (file: string) (prog: TProgram) (z3: Session) : VerifyResult =
    let v = Verifier(file, prog, z3)
    z3.Init()
    v.Prelude()
    let exprFns = prog.Fns |> List.filter (fun f -> f.IsExprFn)
    for f in exprFns |> List.filter (fun f -> not f.IsRecursive) do
        v.Define f
    let recursive = exprFns |> List.filter (fun f -> f.IsRecursive)
    let terminating = recursive |> List.filter (fun f -> f.Decreases.IsSome && v.Termination f)
    for f in terminating do
        v.Define f
    for f in prog.Fns do
        v.Function f
    let withContract = prog.Fns |> List.filter (fun f -> not f.Ensures.IsEmpty)
    let determined = withContract |> List.filter v.Completeness |> List.length
    { Diagnostics = v.Diagnostics; Proved = v.Proved; Determined = determined; WithContract = withContract.Length }
