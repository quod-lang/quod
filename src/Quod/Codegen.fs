/// What the code generators share: an analysis of the verified program, independent of the target.
module Quod.Codegen

open System.Collections.Generic
open Quod.Typed

/// Does this expression build a new list (so that nothing else refers to it)?
let rec fresh (e: TExpr) =
    match e.Kind with
    | ESeq _ | EConcat _ | ESlice _ -> true
    | EIf(_, a, b) -> fresh a && fresh b
    | _ -> false

/// The mutable sequence locals that may be extended in place: `r = r + [e]` as `r.append(e)`
/// instead of a copy (quadratic in a loop). A local qualifies when it always holds a list of its
/// own: every value assigned to it is fresh, and it is never shared, that is never used as a
/// whole except in a concatenation, len, an index, a slice, a comparison, or a return. Then no
/// other variable, argument, tuple or sequence can see the list change.
let appendable (body: TStmt list) (checkedAtRunTime: bool) : Set<string> =
    let candidates = HashSet<string>()
    let shared = HashSet<string>()
    let rec uses (whole: bool) (e: TExpr) =
        let reads = uses true
        let inner = uses false
        match e.Kind with
        | EVar n -> if not whole then shared.Add n |> ignore
        | EConcat(a, b) | EEq(a, b) -> reads a; reads b
        | ELen s -> reads s
        | EConvert a -> inner a
        | EIndex(s, i) -> reads s; inner i
        | ESlice(s, lo, hi) -> reads s; Option.iter inner lo; Option.iter inner hi
        | ESeq xs | ETuple xs | ECall(_, xs) | ECons(_, xs) -> List.iter inner xs
        | EProj(x, _) | EField(x, _, _) | ENeg x | ENot x | EToNat x -> inner x
        | EMatch(x, arms) -> inner x; arms |> List.iter (fun (_, _, b) -> inner b)
        | EArith(_, a, b) | ECmp(_, a, b) | ELogic(_, a, b) -> inner a; inner b
        | EIf(c, a, b) -> inner c; inner a; inner b
        | EQuant(_, _, lo, hi, b) -> inner lo; inner hi; inner b
        | EInt _ | EBool _ | EResult -> ()
    let rec walk (ss: TStmt list) =
        for s in ss do
            match s.Kind with
            | SLet(_, n, _, _) when isLemmaBinding n -> () // erased
            | SLet(isMut, n, ty, v) ->
                (match ty with
                 | TySeq _ when isMut && fresh v -> candidates.Add n |> ignore
                 | _ -> shared.Add n |> ignore) // another variable of that name: leave both alone
                uses false v
            | SAssign(n, v) ->
                if not (fresh v) then shared.Add n |> ignore
                uses false v
            | SIf(c, a, b) -> uses false c; walk a; walk b
            | SWhile(c, invs, _, b) ->
                uses false c
                if checkedAtRunTime then List.iter (uses false) invs
                walk b
            | SAssert e -> if checkedAtRunTime then uses false e
            | SReturn e -> uses true e
    walk body
    candidates |> Seq.filter (fun n -> not (shared.Contains n)) |> Set.ofSeq

/// Does this type hold a `nat` under a sequence, whose check costs a pass over it?
let rec natInList (t: Ty) =
    let rec hasNat t =
        match t with
        | TyNat -> true
        | TySeq e -> hasNat e
        | TyTuple ts -> List.exists hasNat ts
        | _ -> false
    match t with
    | TySeq e -> hasNat e
    | TyTuple ts -> List.exists natInList ts
    | _ -> false

/// A `requires` cheap enough to check at every public call: no quantifier, and no call, which
/// could hide one.
let rec cheap (e: TExpr) =
    match e.Kind with
    | EQuant _ | ECall _ | EMatch _ -> false
    | ECons(_, xs) -> List.forall cheap xs
    | EField(a, _, _) -> cheap a
    | EInt _ | EBool _ | EVar _ | EResult -> true
    | ESeq xs | ETuple xs -> List.forall cheap xs
    | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> cheap a && cheap b
    | ESlice(a, b, c) -> cheap a && Option.forall cheap b && Option.forall cheap c
    | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a | EConvert a -> cheap a
    | EIf(a, b, c) -> cheap a && cheap b && cheap c

// --- modules: the flattened program, seen from one module ---------------------------------------

let rec private mapCalls (rename: string -> string) (e: TExpr) : TExpr =
    let go = mapCalls rename
    let kind =
        match e.Kind with
        | EInt _ | EBool _ | EVar _ | EResult -> e.Kind
        | ESeq xs -> ESeq(List.map go xs)
        | ETuple xs -> ETuple(List.map go xs)
        | EIndex(a, b) -> EIndex(go a, go b)
        | ESlice(a, b, c) -> ESlice(go a, Option.map go b, Option.map go c)
        | EProj(a, k) -> EProj(go a, k)
        | ECons(k, xs) ->
            // visited too: a generator must import the module of a data type it builds
            (match e.Ty with TyData d -> rename d.DataName |> ignore | _ -> ())
            ECons(k, List.map go xs)
        | EField(a, k, i) -> EField(go a, k, i)
        | EMatch(a, arms) ->
            (match a.Ty with TyData d -> rename d.DataName |> ignore | _ -> ())
            EMatch(go a, arms |> List.map (fun (k, n, b) -> k, n, go b))
        | ELen a -> ELen(go a)
        | ECall(f, args) -> ECall(rename f, List.map go args)
        | ENeg a -> ENeg(go a)
        | ENot a -> ENot(go a)
        | EArith(op, a, b) -> EArith(op, go a, go b)
        | EConcat(a, b) -> EConcat(go a, go b)
        | ECmp(op, a, b) -> ECmp(op, go a, go b)
        | EEq(a, b) -> EEq(go a, go b)
        | ELogic(op, a, b) -> ELogic(op, go a, go b)
        | EIf(a, b, c) -> EIf(go a, go b, go c)
        | EQuant(q, v, a, b, c) -> EQuant(q, v, go a, go b, go c)
        | EToNat a -> EToNat(go a)
        | EConvert a -> EConvert(go a)
    { e with Kind = kind }

let rec private mapCallsS (rename: string -> string) (s: TStmt) : TStmt =
    let e = mapCalls rename
    let block = List.map (mapCallsS rename)
    let kind =
        match s.Kind with
        | SLet(m, n, t, v) -> SLet(m, n, t, e v)
        | SAssign(n, v) -> SAssign(n, e v)
        | SIf(c, a, b) -> SIf(e c, block a, block b)
        | SWhile(c, invs, d, b) -> SWhile(e c, List.map e invs, e d, block b)
        | SAssert x -> SAssert(e x)
        | SReturn x -> SReturn(e x)
    { s with Kind = kind }

/// The imported modules of a flattened program, in the order of their functions.
let importedModules (prog: TProgram) : string list =
    (prog.Types |> List.map (fun d -> d.DataName)) @ (prog.Fns |> List.map (fun f -> f.Name))
    |> List.choose (fun n -> fst (Quod.Modules.split n))
    |> List.distinct

/// The functions of one module (None: the file itself) under their short names. A call to another
/// module keeps its full name, by which the generators know it is one.
let moduleView (name: string option) (prog: TProgram) : TProgram =
    let prefix = match name with Some m -> m + "." | None -> ""
    let mine (f: string) = fst (Quod.Modules.split f) = name
    let short (f: string) = if mine f then f.Substring prefix.Length else f
    let e = mapCalls short
    { Types = prog.Types |> List.filter (fun d -> mine d.DataName)
      Fns =
        prog.Fns
        |> List.filter (fun f -> mine f.Name)
        |> List.map (fun f ->
            { f with
                Name = short f.Name
                Requires = List.map e f.Requires
                Ensures = List.map e f.Ensures
                Loose = f.Loose |> Option.map (fun l -> { l with Relation = e l.Relation })
                Decreases = Option.map e f.Decreases
                Body =
                    match f.Body with
                    | TExprBody x -> TExprBody(e x)
                    | TStmtBody items -> TStmtBody(List.map (mapCallsS short) items) }) }

let private moduleViewCalls (visit: string -> string) (view: TProgram) =
    let e = mapCalls visit >> ignore
    for f in view.Fns do
        List.iter e f.Requires
        List.iter e f.Ensures
        f.Loose |> Option.iter (fun l -> e l.Relation)
        Option.iter e f.Decreases
        match f.Body with
        | TExprBody x -> e x
        | TStmtBody items -> items |> List.iter (mapCallsS visit >> ignore)

/// The modules a view calls, in a stable order.
let calledModules (view: TProgram) : string list =
    let found = HashSet<string>()
    let rename (f: string) =
        (match fst (Quod.Modules.split f) with Some m -> found.Add m |> ignore | None -> ())
        f
    moduleViewCalls rename view
    // its own data types are not an import
    let own = view.Types |> List.choose (fun d -> fst (Quod.Modules.split d.DataName)) |> Set.ofList
    found |> Seq.filter (fun m -> not (own.Contains m)) |> Seq.sort |> List.ofSeq

