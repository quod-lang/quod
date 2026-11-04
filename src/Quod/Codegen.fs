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
        | EIndex(s, i) -> reads s; inner i
        | ESlice(s, lo, hi) -> reads s; Option.iter inner lo; Option.iter inner hi
        | ESeq xs | ETuple xs | ECall(_, xs) -> List.iter inner xs
        | EProj(x, _) | ENeg x | ENot x | EToNat x -> inner x
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
