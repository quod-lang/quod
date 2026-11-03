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

/// Sequences are axiomatized, as Dafny does: uninterpreted functions, one set per element sort
/// (q.len.i, q.nth.i, q.cat.TiiE...), described by triggered axioms. Z3's sequence theory is not
/// used. It does not carry a quantified fact about r over to r[..n] + [x] (it never creates the
/// term r[i] that would trigger the fact), and even bridged to the axioms it made proofs
/// unstable: each small change of the encoding fixed one program and broke another. The sort
/// stays Z3's Seq, but only as a carrier; models are read through q.len and q.nth.
let private seqOp (op: string) (seqTy: Ty) =
    match seqTy with
    | TySeq e -> "q." + op + "." + tySig e
    | _ -> "q." + op + ".i"

/// Declarations and axioms of the wrappers for sequences of `elem`.
let private seqAxioms (elem: Ty) : string list =
    let s = sortOf (TySeq elem)
    let e = sortOf elem
    let f op = seqOp op (TySeq elem)
    let len, nth, cat, ext, unit, eq, empty = f "len", f "nth", f "cat", f "ext", f "unit", f "eq", f "empty"
    let forall (binders: string) (body: string) (pattern: string) =
        "(assert (forall (" + binders + ") (! " + body + " :pattern (" + pattern + "))))"
    [ "(declare-fun " + len + " (" + s + ") Int)"
      "(declare-fun " + nth + " (" + s + " Int) " + e + ")"
      "(declare-fun " + cat + " (" + s + " " + s + ") " + s + ")"
      "(declare-fun " + ext + " (" + s + " Int Int) " + s + ")"
      "(declare-fun " + unit + " (" + e + ") " + s + ")"
      "(declare-fun " + eq + " (" + s + " " + s + ") Bool)"
      // equality, written q.eq in the program's formulas: extensional, so that two sequences
      // with the same length and elements are known to be equal (Dafny's Seq#Equal)
      forall ("(a " + s + ") (b " + s + ")")
          ("(and (= (" + eq + " a b) (= a b)) (= (" + eq + " a b) (and (= (" + len + " a) (" + len + " b)) (forall ((i Int)) (=> (and (<= 0 i) (< i (" + len + " a))) (= (" + nth + " a i) (" + nth + " b i)))))))")
          ("(" + eq + " a b)")
      "(declare-fun " + empty + " () " + s + ")"
      "(assert (= (" + len + " " + empty + ") 0))"
      forall ("(a " + s + ")") ("(and (>= (" + len + " a) 0) (=> (= (" + len + " a) 0) (= a " + empty + ")))") ("(" + len + " a)")
      // concatenation: associative (oriented to the right, so it cannot loop), [] is neutral
      forall ("(a " + s + ") (b " + s + ") (c " + s + ")") ("(= (" + cat + " (" + cat + " a b) c) (" + cat + " a (" + cat + " b c)))") ("(" + cat + " (" + cat + " a b) c)")
      forall ("(a " + s + ") (b " + s + ")") ("(and (=> (= (" + len + " b) 0) (= (" + cat + " a b) a)) (=> (= (" + len + " a) 0) (= (" + cat + " a b) b)))") ("(" + cat + " a b)")      // lengths and elements of the results, in terms of the operands
      forall ("(a " + s + ") (b " + s + ")") ("(= (" + len + " (" + cat + " a b)) (+ (" + len + " a) (" + len + " b)))") ("(" + len + " (" + cat + " a b))")
      forall ("(a " + s + ") (b " + s + ") (i Int)")
          ("(=> (and (<= 0 i) (< i (+ (" + len + " a) (" + len + " b)))) (= (" + nth + " (" + cat + " a b) i) (ite (< i (" + len + " a)) (" + nth + " a i) (" + nth + " b (- i (" + len + " a))))))")
          ("(" + nth + " (" + cat + " a b) i)")
      forall ("(a " + s + ") (lo Int) (n Int)") ("(=> (and (<= 0 lo) (<= 0 n) (<= (+ lo n) (" + len + " a))) (= (" + len + " (" + ext + " a lo n)) n))") ("(" + len + " (" + ext + " a lo n))")
      forall ("(a " + s + ") (lo Int) (n Int) (i Int)")
          ("(=> (and (<= 0 lo) (<= 0 i) (< i n) (<= (+ lo n) (" + len + " a))) (= (" + nth + " (" + ext + " a lo n) i) (" + nth + " a (+ lo i))))")
          ("(" + nth + " (" + ext + " a lo n) i)")
      forall ("(x " + e + ")") ("(and (= (" + len + " (" + unit + " x)) 1) (= (" + nth + " (" + unit + " x) 0) x))") ("(" + unit + " x)")
      // slices of a concatenation, and the whole slice, as terms: decode(r + [p]) unfolds into
      // decode((r + [p])[..len(r)]), which these make decode(r) without an assert
      forall ("(a " + s + ") (b " + s + ") (lo Int) (n Int)")
          ("(and (=> (and (<= 0 lo) (<= 0 n) (<= (+ lo n) (" + len + " a))) (= (" + ext + " (" + cat + " a b) lo n) (" + ext + " a lo n))) "
           + "(=> (and (<= (" + len + " a) lo) (<= 0 n) (<= (+ lo n) (+ (" + len + " a) (" + len + " b)))) (= (" + ext + " (" + cat + " a b) lo n) (" + ext + " b (- lo (" + len + " a)) n))))")
          ("(" + ext + " (" + cat + " a b) lo n)")
      forall ("(a " + s + ") (lo Int) (n Int)") ("(=> (and (= lo 0) (= n (" + len + " a))) (= (" + ext + " a lo n) a))") ("(" + ext + " a lo n)")
      // a slice one element longer than another slice already present: xs[..k + 1] is
      // xs[..k] + [xs[k]], the step of every loop that walks a prefix. Triggered only by two
      // existing slices, so it creates no new slice and cannot loop.
      forall ("(a " + s + ") (lo Int) (m Int) (n Int)")
          ("(=> (and (<= 0 lo) (<= 0 m) (= n (+ m 1)) (<= (+ lo n) (" + len + " a))) (= (" + ext + " a lo n) (" + cat + " (" + ext + " a lo m) (" + unit + " (" + nth + " a (+ lo m))))))")
          ("(" + ext + " a lo m) (" + ext + " a lo n)") ]

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
        match typeFacts fresh e ("(" + seqOp "nth" t + " " + term + " " + q + ")") with
        | [] -> []
        | fs -> [ "(forall ((" + q + " Int)) (=> (and (<= 0 " + q + ") (< " + q + " (" + seqOp "len" t + " " + term + "))) " + conj fs + "))" ]
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

let private constRx = Text.RegularExpressions.Regex(@"[A-Za-z_][A-Za-z0-9_]*@[0-9]+")
let private boundRx = Text.RegularExpressions.Regex(@"\(\(([A-Za-z_][A-Za-z0-9_]*@[0-9]+) ")

/// Inside a loop, the facts about constants no longer in use (r@1 = [], i@2 = 0: the versions
/// before the loop of the variables it modifies, and older ones) are useless, and they mislead
/// Z3: removing r@1 = [] turned a timeout of the rle_encode invariant into a proof in 0.1 s. A
/// fact about a dead constant is kept only when it leads, through dead constants, to a local
/// variable still in use (let n = len(r) before the loop keeps r@1 = [] and n == 0); facts
/// about live constants only are all kept. Parameters do not count as links: every invariant
/// mentions them. Dropping facts is always sound.
let private relevantFacts (live: Set<string>) (roots: Set<string>) (facts: string list) : string list =
    let constsOf (fact: string) =
        let bound = boundRx.Matches fact |> Seq.map (fun m -> m.Groups.[1].Value) |> Set.ofSeq
        constRx.Matches fact |> Seq.map (fun m -> m.Value) |> Seq.filter (fun c -> not (bound.Contains c)) |> Set.ofSeq
    let withConsts = facts |> List.map (fun f -> f, constsOf f, constsOf f |> Set.filter (fun c -> not (live.Contains c)))
    let needed = HashSet<string>(roots)
    let kept = HashSet<string>()
    let mutable changed = true
    while changed do
        changed <- false
        for (fact, cs, dead) in withConsts do
            if not (kept.Contains fact) && (dead.IsEmpty || cs |> Set.exists needed.Contains) then
                kept.Add fact |> ignore
                for c in dead do
                    if needed.Add c then changed <- true
                changed <- true
    facts |> List.filter kept.Contains

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

/// z3's reason-unknown answer, `(:reason-unknown "(incomplete quantifiers)")`, as its text:
/// `incomplete quantifiers`.
let private reasonText (answer: string) =
    let a, b = answer.IndexOf '"', answer.LastIndexOf '"'
    let text = if a >= 0 && b > a then answer.Substring(a + 1, b - a - 1).Trim() else ""
    let text = if text.StartsWith "(" && text.EndsWith ")" then text.Substring(1, text.Length - 2).Trim() else text
    if text = "" then "unknown" else text

// --- concrete witness search ------------------------------------------------------------

/// Small values of a type, for candidate results: [], singletons, pairs of small elements.
let rec private smallValues (t: Ty) : Eval.Value list =
    match t with
    | TyInt | TyError -> [ 0; 1; -1; 2; 3 ] |> List.map (fun n -> Eval.VInt(bigint (n: int)))
    | TyNat -> [ 0; 1; 2; 3 ] |> List.map (fun n -> Eval.VInt(bigint (n: int)))
    | TyBool -> [ Eval.VBool false; Eval.VBool true ]
    | TyTuple ts ->
        ts
        |> List.fold (fun acc ct -> [ for prefix in acc do for v in smallValues ct -> prefix @ [ v ] ]) [ [] ]
        |> List.truncate 30
        |> List.map Eval.VTuple
    | TySeq e ->
        let elems = smallValues e |> List.truncate 12
        [ Eval.VSeq [] ] @ [ for x in elems -> Eval.VSeq [ x ] ] @ ([ for x in elems do for y in elems -> Eval.VSeq [ x; y ] ] |> List.truncate 20)

/// The simplest value of a type: 0, false, [], a tuple of those (an edge case worth running).
let rec private zeroValue (t: Ty) : Eval.Value =
    match t with
    | TyInt | TyNat | TyError -> Eval.VInt(bigint 0)
    | TyBool -> Eval.VBool false
    | TySeq _ -> Eval.VSeq []
    | TyTuple ts -> Eval.VTuple(ts |> List.map zeroValue)

/// A random small value of a type, for inputs (ints in -6..6, sequences of length 0..5).
let rec private randomValue (rnd: Random) (t: Ty) : Eval.Value =
    match t with
    | TyInt | TyError -> Eval.VInt(bigint (rnd.Next(-6, 7)))
    | TyNat -> Eval.VInt(bigint (rnd.Next(0, 7)))
    | TyBool -> Eval.VBool(rnd.Next 2 = 0)
    | TySeq e -> Eval.VSeq [ for _ in 1 .. rnd.Next(0, 6) -> randomValue rnd e ]
    | TyTuple ts -> Eval.VTuple(ts |> List.map (randomValue rnd))

/// The integer literals of the program, and their neighbours: a bug triggered by `n == 1000`
/// is out of reach of small random inputs (external counter-review). Small ones are left out
/// (-6..6 is drawn anyway); at most 30 values.
let private programConstants (prog: TProgram) : bigint list =
    let found = HashSet<bigint>()
    let rec expr (e: TExpr) =
        match e.Kind with
        | EInt n -> found.Add n |> ignore
        | ESeq xs | ETuple xs | ECall(_, xs) -> List.iter expr xs
        | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> expr a; expr b
        | ESlice(a, b, c) -> expr a; Option.iter expr b; Option.iter expr c
        | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a -> expr a
        | EIf(a, b, c) | EQuant(_, _, a, b, c) -> expr a; expr b; expr c
        | EBool _ | EVar _ | EResult -> ()
    let rec stmt (s: TStmt) =
        match s.Kind with
        | SLet(_, _, _, e) | SAssign(_, e) | SAssert e | SReturn e -> expr e
        | SIf(c, a, b) -> expr c; List.iter stmt a; List.iter stmt b
        | SWhile(c, invs, d, b) -> expr c; List.iter expr invs; expr d; List.iter stmt b
    for f in prog.Fns do
        f.Requires @ f.Ensures |> List.iter expr
        match f.Body with
        | TExprBody e -> expr e
        | TStmtBody ss -> List.iter stmt ss
    found
    |> Seq.collect (fun c -> [ c - 1I; c; c + 1I ])
    |> Seq.filter (fun c -> abs c > 6I)
    |> Seq.distinct
    |> Seq.sort
    |> Seq.truncate 30
    |> List.ofSeq

/// A random input: like randomValue, but an int is one of the program's constants one time
/// in three (when there are any).
let rec private inputValue (rnd: Random) (pool: bigint list) (t: Ty) : Eval.Value =
    let fromPool (ok: bigint -> bool) =
        match pool |> List.filter ok with
        | [] -> None
        | cs when rnd.Next 3 = 0 -> Some(Eval.VInt cs.[rnd.Next cs.Length])
        | _ -> None
    match t with
    | TyInt | TyError -> fromPool (fun _ -> true) |> Option.defaultWith (fun () -> randomValue rnd t)
    | TyNat -> fromPool (fun c -> c.Sign >= 0) |> Option.defaultWith (fun () -> randomValue rnd t)
    | TySeq e ->
        // one time in three, a length among the program's constants (requires len(xs) == 9)
        let lengths = pool |> List.filter (fun c -> c.Sign > 0 && c <= 50I)
        let n = if not lengths.IsEmpty && rnd.Next 3 = 0 then int lengths.[rnd.Next lengths.Length] else rnd.Next(0, 6)
        Eval.VSeq [ for _ in 1 .. n -> inputValue rnd pool e ]
    | TyTuple ts -> Eval.VTuple(ts |> List.map (inputValue rnd pool))
    | TyBool -> randomValue rnd t

/// Does e mention the variable `name`? (By the text of e: a whole word.)
let private mentions (name: string) (e: TExpr) =
    Text.RegularExpressions.Regex.IsMatch(Printer.exprText (toSyntax e), @"\b" + Text.RegularExpressions.Regex.Escape name + @"\b")

/// Parameters that the requires define from the others, so that random inputs can satisfy them:
/// `p == E`, or `len(p) == E` with `forall k in 0..E2: p[k] == F`. Random values almost never
/// satisfy `forall k in 0..len(xs) + 1: ps[k] == sum(xs, 0, k)`; built from xs, they always do.
/// Returns a function that rewrites the defined parameters of an input.
let private definedParams (f: TFn) (ev: Eval.Evaluator) : Map<string, Eval.Value> -> Map<string, Eval.Value> =
    let rec conjuncts (e: TExpr) =
        match e.Kind with
        | ELogic(OAnd, a, b) -> conjuncts a @ conjuncts b
        | _ -> [ e ]
    let parts = f.Requires |> List.collect conjuncts
    let isParam (n: string) = f.Params |> List.exists (fun p -> p.Name = n)
    let direct =
        parts |> List.choose (fun r ->
            match r.Kind with
            | EEq({ Kind = EVar p }, v) | EEq(v, { Kind = EVar p }) when isParam p && not (mentions p v) -> Some(p, v)
            | _ -> None)
    let elementwise =
        parts |> List.choose (fun r ->
            match r.Kind with
            | EQuant(Syntax.Forall, k, lo, hi, body) ->
                match body.Kind with
                | EEq({ Kind = EIndex({ Kind = EVar p }, { Kind = EVar k2 }) }, v)
                | EEq(v, { Kind = EIndex({ Kind = EVar p }, { Kind = EVar k2 }) }) when k2 = k && isParam p && not (mentions p v) && not (mentions p hi) ->
                    Some(p, k, lo, hi, v)
                | _ -> None
            | _ -> None)
    fun (env: Map<string, Eval.Value>) ->
        let mutable env = env
        for (p, v) in direct do
            try env <- env.Add(p, ev.Expr(v, env)) with Eval.CannotEvaluate _ -> ()
        for (p, k, lo, hi, v) in elementwise do
            try
                match ev.Expr(lo, env), ev.Expr(hi, env) with
                | Eval.VInt l, Eval.VInt h when l.IsZero && h.Sign >= 0 && h <= bigint 50 ->
                    env <- env.Add(p, Eval.VSeq [ for i in 0 .. int h - 1 -> ev.Expr(v, env.Add(k, Eval.VInt(bigint i))) ])
                | _ -> ()
            with Eval.CannotEvaluate _ -> ()
        env

let rec private assignedIn (body: TStmt list) : string list =
    body |> List.collect (fun s ->
        match s.Kind with
        | SAssign(n, _) -> [ n ]
        | SIf(_, a, b) -> assignedIn a @ assignedIn b
        | SWhile(_, _, _, b) -> assignedIn b
        | _ -> [])

// --- inputs from the solver, at a fixed length -------------------------------------------

/// A value in a bounded problem: sequences have a known length, so a quantifier over a known
/// range unfolds into a conjunction and `len` is a number. Scalars are SMT terms, or numbers
/// and booleans when known (so that ranges and lengths stay known).
type private BVal =
    | BInt of bigint
    | BBool of bool
    | BTerm of string
    | BSeq of BVal list
    | BTup of BVal list

/// What the bounded translation does not cover (a call, a slice with unknown bounds...): the
/// conjunct is left out. Inputs are checked by the evaluator anyway.
exception private Unbounded

let private bterm (b: BVal) : string =
    match b with
    | BInt n -> if n.Sign < 0 then "(- " + (-n).ToString() + ")" else n.ToString()
    | BBool v -> if v then "true" else "false"
    | BTerm t -> t
    | BSeq _ | BTup _ -> raise Unbounded

let rec private bexpr (env: Map<string, BVal>) (e: TExpr) : BVal =
    let go = bexpr env
    let known (x: BVal) = match x with BInt n -> n | _ -> raise Unbounded
    let items (x: BVal) = match x with BSeq l -> l | _ -> raise Unbounded
    let rec equal (a: BVal) (b: BVal) : BVal =
        match a, b with
        | BSeq l1, BSeq l2 -> if l1.Length <> l2.Length then BBool false else conjB (List.map2 equal l1 l2)
        | BTup l1, BTup l2 -> conjB (List.map2 equal l1 l2)
        | BInt x, BInt y -> BBool(x = y)
        | BBool x, BBool y -> BBool(x = y)
        | _ -> BTerm("(= " + bterm a + " " + bterm b + ")")
    and conjB (parts: BVal list) =
        if parts |> List.exists (fun p -> p = BBool false) then BBool false
        else
            match parts |> List.filter (fun p -> p <> BBool true) with
            | [] -> BBool true
            | [ p ] -> p
            | ps -> BTerm("(and " + String.Join(" ", ps |> List.map bterm) + ")")
    let disjB (parts: BVal list) =
        if parts |> List.exists (fun p -> p = BBool true) then BBool true
        else
            match parts |> List.filter (fun p -> p <> BBool false) with
            | [] -> BBool false
            | [ p ] -> p
            | ps -> BTerm("(or " + String.Join(" ", ps |> List.map bterm) + ")")
    match e.Kind with
    | EInt n -> BInt n
    | EBool b -> BBool b
    | EVar n -> (match env.TryFind n with Some v -> v | None -> raise Unbounded)
    | ESeq xs -> BSeq(List.map go xs)
    | ETuple xs -> BTup(List.map go xs)
    | ELen s -> BInt(bigint (items (go s)).Length)
    | EIndex(s, i) ->
        let l = items (go s)
        match go i with
        | BInt k -> if k.Sign >= 0 && k < bigint l.Length then l.[int k] else raise Unbounded
        | idx when not l.IsEmpty && l |> List.forall (fun x -> match x with BSeq _ | BTup _ -> false | _ -> true) ->
            // an unknown index: the element it picks (out of bounds, the last one: such an
            // input fails the evaluator's check of the requires)
            let t = bterm idx
            let last = bterm (List.last l)
            BTerm(List.foldBack (fun (k, x) acc -> "(ite (= " + t + " " + string k + ") " + bterm x + " " + acc + ")") (List.indexed l |> List.take (l.Length - 1)) last)
        | _ -> raise Unbounded
    | ESlice(s, lo, hi) ->
        let l = items (go s)
        let a = lo |> Option.map (go >> known) |> Option.defaultValue 0I
        let b = hi |> Option.map (go >> known) |> Option.defaultValue (bigint l.Length)
        if a.Sign < 0 || a > b || b > bigint l.Length then raise Unbounded
        BSeq(l |> List.skip (int a) |> List.take (int (b - a)))
    | EProj(t, k) -> (match go t with BTup l -> l.[k] | _ -> raise Unbounded)
    | ECall _ | EResult -> raise Unbounded
    | ENeg x -> (match go x with BInt n -> BInt(-n) | v -> BTerm("(- " + bterm v + ")"))
    | ENot x -> (match go x with BBool b -> BBool(not b) | v -> BTerm("(not " + bterm v + ")"))
    | EArith(op, a, b) ->
        match go a, go b, op with
        | BInt x, BInt y, OAdd -> BInt(x + y)
        | BInt x, BInt y, OSub -> BInt(x - y)
        | BInt x, BInt y, OMul -> BInt(x * y)
        | BInt x, BInt y, (ODiv | OMod) when not y.IsZero ->
            let q, r = Eval.euclidDivMod x y
            BInt(if op = ODiv then q else r)
        | x, y, _ ->
            let o = match op with OAdd -> "+" | OSub -> "-" | OMul -> "*" | ODiv -> "div" | OMod -> "mod"
            BTerm("(" + o + " " + bterm x + " " + bterm y + ")")
    | EConcat(a, b) -> BSeq(items (go a) @ items (go b))
    | ECmp(op, a, b) ->
        match go a, go b with
        | BInt x, BInt y -> BBool(match op with OLt -> x < y | OLe -> x <= y | OGt -> x > y | OGe -> x >= y)
        | x, y ->
            let o = match op with OLt -> "<" | OLe -> "<=" | OGt -> ">" | OGe -> ">="
            BTerm("(" + o + " " + bterm x + " " + bterm y + ")")
    | EEq(a, b) -> equal (go a) (go b)
    | ELogic(op, a, b) ->
        match op with
        | OAnd -> conjB [ go a; go b ]
        | OOr -> disjB [ go a; go b ]
        | OImplies ->
            match go a with
            | BBool false -> BBool true
            | BBool true -> go b
            | x -> BTerm("(=> " + bterm x + " " + bterm (go b) + ")")
        | OIff -> equal (go a) (go b)
    | EIf(c, a, b) ->
        match go c with
        | BBool true -> go a
        | BBool false -> go b
        | cv -> BTerm("(ite " + bterm cv + " " + bterm (go a) + " " + bterm (go b) + ")")
    | EQuant(q, name, lo, hi, body) ->
        let a, b = known (go lo), known (go hi)
        if b - a > 60I then raise Unbounded
        let parts = [ for i in a .. b - 1I -> bexpr (env.Add(name, BInt i)) body ]
        match q with
        | Syntax.Forall -> conjB parts
        | Syntax.Exists -> disjB parts
    | EToNat x -> go x

/// The `if`s of a function's body (statements and expressions), by their span, in order.
let private ifSpans (f: TFn) : Span list =
    let found = ResizeArray<Span>()
    let rec expr (e: TExpr) =
        match e.Kind with
        | EIf(c, a, b) -> found.Add e.Span; expr c; expr a; expr b
        | ESeq xs | ETuple xs | ECall(_, xs) -> List.iter expr xs
        | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> expr a; expr b
        | ESlice(a, b, c) -> expr a; Option.iter expr b; Option.iter expr c
        | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a -> expr a
        | EQuant _ | EInt _ | EBool _ | EVar _ | EResult -> ()
    let rec stmt (st: TStmt) =
        match st.Kind with
        | SLet(_, _, _, e) | SAssign(_, e) | SReturn e -> expr e
        | SIf(c, a, b) -> found.Add st.Span; expr c; List.iter stmt a; List.iter stmt b
        | SWhile(c, _, _, b) -> expr c; List.iter stmt b
        | SAssert _ -> ()
    match f.Body with
    | TExprBody e -> expr e
    | TStmtBody ss -> List.iter stmt ss
    List.ofSeq found

// --- the verifier ---------------------------------------------------------------------

type private Verifier(file: string, prog: TProgram, z3: Session, budgetMs: int) =
    let fns = prog.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList
    let diags = ResizeArray<Diagnostic>()
    let mutable counter = 0
    let mutable proved = 0
    let mutable current: FnInfo option = None
    let paramsOf = Dictionary<string, (string * Ty) list>()
    /// Obligations of the current function broken by running it on small inputs, with the inputs
    /// (see RunConcrete), and how many inputs were run.
    let concrete = Dictionary<string * Span, (string * string) list>()
    let mutable concreteRuns = 0
    /// The time budget of the whole check (0: none). Past it, obligations are not sent to the
    /// solver: they are counted as not attempted, per function (external counter-review: an
    /// agent waits for `quod check` as a whole, N obligations at 2T + 5 s each add up).
    let clock = Diagnostics.Stopwatch.StartNew()
    let mutable skippedHere = 0
    let mutable skipped = 0
    /// The sort of each integer or boolean constant (to declare it again elsewhere), and a second
    /// z3 process without the axioms of the program, started when first needed (see Isolated).
    let scalarSorts = Dictionary<string, string>()
    let mutable arith: Session option = None
    /// Told before and after each try of the solver (`quod mcp` turns a long one into a progress
    /// notification)
    let mutable beforeSolver: string -> unit = ignore
    let mutable afterSolver: unit -> unit = ignore
    /// Inputs tried (valid or not), for the message when few satisfy the requires.
    let mutable concreteTries = 0
    /// The branches of the current function that no run took ("line 4 (condition true)").
    let mutable untaken: string list = []
    let constants = programConstants prog

    member _.Diagnostics = List.ofSeq diags
    member _.NotAttempted = skipped
    member _.BeforeSolver with set (f: string -> unit) = beforeSolver <- f
    member _.AfterSolver with set (f: unit -> unit) = afterSolver <- f

    /// Stop the second z3 process, if one was started.
    member _.Close() =
        arith |> Option.iter (fun (a: Session) -> (a :> IDisposable).Dispose())
        arith <- None

    /// Milliseconds left in the budget (None: no budget).
    member _.Remaining : int option =
        if budgetMs <= 0 then None else Some(budgetMs - int clock.ElapsedMilliseconds)

    member v.OverBudget = match v.Remaining with Some r -> r <= 0 | None -> false

    /// Check, with the time limit cut to what is left of the budget.
    member v.BudgetedCheck(check: unit -> CheckResult) : CheckResult =
        match v.Remaining with
        | Some r when r < z3.DefaultTimeout ->
            z3.SetTimeout(max 1 r)
            let answer = check ()
            z3.SetTimeout z3.DefaultTimeout
            answer
        | _ -> check ()

    /// One diagnostic for the obligations of a function past the budget.
    member v.ReportSkipped(f: TFn) =
        if skippedHere > 0 then
            diags.Add
                { File = file; Span = f.Span; Kind = "proof"; Status = "not-attempted"; Severity = Error
                  Fn = Some f.Name; Property = Some "time budget"; Counterexample = []; Reason = Some "budget"; Evidence = None
                  Message =
                    string skippedHere + " proof obligation(s) not attempted: the time budget of the check ("
                    + string (budgetMs / 1000) + " s) was used up before them. Check this function in a file of its own, or raise the budget "
                    + "(the budget argument of quod_check through MCP, --budget on the command line)" }
            skippedHere <- 0
    member _.Proved = proved

    member _.Fresh(prefix: string) =
        counter <- counter + 1
        prefix + "@" + string counter

    member v.FreshQ() = v.Fresh "q"

    /// Declare a new SMT constant of type t and return its name.
    member v.Const(baseName: string, t: Ty) : string =
        let name = v.Fresh baseName
        z3.Send("(declare-const " + name + " " + sortOf t + ")")
        match t with
        | TyInt | TyNat | TyBool -> scalarSorts.[name] <- sortOf t
        | _ -> ()
        name

    /// The obligation again, without the axioms of the program, when it is about integers and
    /// booleans only. The axioms of sequences are quantified, and with them in the context z3 no
    /// longer uses its solver for nonlinear arithmetic: `a == b * b * b` was refuted in 0.04 s
    /// alone in its file, and timed out next to a function on sequences (first-user test of
    /// 0.1.1). The facts that mention anything else are left out: a proof with fewer facts is
    /// still a proof, but a model of fewer facts is a counterexample only if none was left out.
    /// Some(result, counterexample) when this says more than the shared session did.
    member v.Isolated(st: State, o: Obligation, onlyComplete: bool) : (CheckResult * (string * Eval.Value) list) option =
        let operators =
            set [ "and"; "or"; "not"; "=>"; "="; "<"; "<="; ">"; ">="; "+"; "-"; "*"; "div"; "mod"; "ite"
                  "true"; "false"; "distinct"; "abs" ]
        let symbols (term: string) =
            term.Replace("(", " ").Replace(")", " ").Split([| ' '; '\n'; '\t'; '\r' |], StringSplitOptions.RemoveEmptyEntries)
            |> Array.filter (fun t -> not (operators.Contains t) && not (Char.IsDigit t.[0]))
        let scalar (term: string) = symbols term |> Array.forall scalarSorts.ContainsKey
        let kept = if scalar o.Goal then st.Assume |> List.filter scalar else []
        let complete = kept.Length = st.Assume.Length
        if not (scalar o.Goal) || v.OverBudget || (onlyComplete && not complete) then None
        else
            let a =
                match arith with
                | Some a -> a
                | None ->
                    let a = z3.Fork()
                    arith <- Some a
                    a
            a.Push()
            for c in (o.Goal :: kept) |> Seq.collect symbols |> Seq.distinct do
                a.Send("(declare-const " + c + " " + scalarSorts.[c] + ")")
            for f in List.rev kept do
                a.Send("(assert " + f + ")")
            a.Send("(assert (not " + o.Goal + "))")
            // the usual time limit, within the budget: with all its facts this is the only try (the
            // shared session holds the same problem, plus axioms that cannot help); without, a second
            // try after a quick "unknown" of the shared session (test of 0.1.2: a hard obligation
            // cost 2 x timeout + 1 s, so fewer functions fitted in a budget)
            let limit = min a.DefaultTimeout (defaultArg v.Remaining Int32.MaxValue)
            a.SetTimeout(max 1 limit)
            let answer = a.Check()
            a.SetTimeout a.DefaultTimeout
            let outcome =
                match answer with
                | Unsat -> Some(Unsat, [])
                | Unknown _ when complete -> Some(answer, []) // the verdict: the shared session is not tried
                | Sat when complete ->
                    // the parameters this obligation is about, from the second process's model
                    let ps =
                        paramsOf.[current.Value.Fn.Name]
                        |> List.filter (fun (sym, _) -> scalarSorts.ContainsKey sym && (o.Goal :: kept |> List.exists (fun f -> (symbols f) |> Array.contains sym)))
                    let values = a.Values(ps |> List.map fst)
                    let cex =
                        List.zip ps (if values.Length = ps.Length then values else [])
                        |> List.choose (fun ((sym, ty), x) ->
                            valueOf ty x |> Option.map (fun value -> sym.Substring(0, sym.IndexOf '@'), value))
                    Some(Sat, cex)
                | _ -> None
            a.Pop()
            outcome

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
        | ESeq [] -> seqOp "empty" e.Ty
        | ESeq xs ->
            let units = xs |> List.map (fun x -> "(" + seqOp "unit" e.Ty + " " + go x + ")")
            List.reduceBack (fun a b -> "(" + seqOp "cat" e.Ty + " " + a + " " + b + ")") units
        | ETuple xs -> app ("mk_" + tupleName (xs |> List.map (fun x -> x.Ty))) (xs |> List.map go)
        | EIndex(s, i) ->
            let ts, ti = go s, go i
            ob ("(and (<= 0 " + ti + ") (< " + ti + " (" + seqOp "len" s.Ty + " " + ts + ")))") "index in bounds" e.Span
            "(" + seqOp "nth" s.Ty + " " + ts + " " + ti + ")"
        | ESlice(s, lo, hi) ->
            let ts = go s
            let len = "(" + seqOp "len" s.Ty + " " + ts + ")"
            let tlo = lo |> Option.map go |> Option.defaultValue "0"
            let thi = hi |> Option.map go |> Option.defaultValue len
            ob ("(and (<= 0 " + tlo + ") (<= " + tlo + " " + thi + ") (<= " + thi + " " + len + "))")
                "slice bounds (0 <= lo <= hi <= len)" e.Span
            "(" + seqOp "ext" s.Ty + " " + ts + " " + tlo + " (- " + thi + " " + tlo + "))"
        | EProj(t, k) ->
            match t.Ty with
            | TyTuple ts -> "(" + tupleName ts + "_" + string k + " " + go t + ")"
            | _ -> failwith "internal: projection of a non-tuple"
        | ELen s -> "(" + seqOp "len" s.Ty + " " + go s + ")"
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
        | EConcat(a, b) -> "(" + seqOp "cat" e.Ty + " " + go a + " " + go b + ")"
        | ECmp(op, a, b) ->
            let o = match op with OLt -> "<" | OLe -> "<=" | OGt -> ">" | OGe -> ">="
            "(" + o + " " + go a + " " + go b + ")"
        | EEq(a, b) ->
            match a.Ty with
            | TySeq _ -> "(" + seqOp "eq" a.Ty + " " + go a + " " + go b + ")"
            | _ -> "(= " + go a + " " + go b + ")"
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

    /// Run the function on small inputs that satisfy its requires (edge values first, then
    /// random ones), checking every obligation on the way. A broken one is a confirmed
    /// counterexample, found in milliseconds where the solver may only time out: Check reports
    /// it without asking the solver. Nothing found proves nothing; the solver decides.
    member v.RunConcrete(f: TFn) =
        concrete.Clear()
        concreteRuns <- 0
        concreteTries <- 0
        untaken <- []
        Eval.withBigStack (fun () -> v.RunConcreteOnThisThread f)

    /// Inputs that satisfy the requires, found by the solver when random ones rarely do (a
    /// quantified requires: four strictly increasing values from 10 up). For each length 0..6
    /// of the sequence parameters, a sequence is that many unknowns, so the requires unfolds
    /// into a formula without quantifiers, easy for the solver (external counter-review). A
    /// random bound on one unknown varies the inputs from one try to the next.
    member private v.SolverInputs(f: TFn, rnd: Random) : Eval.Value list list =
        let scalar (t: Ty) = match t with TyInt | TyNat | TyBool -> true | _ -> false
        let supported (t: Ty) =
            match t with
            | TyTuple ts -> List.forall scalar ts
            | TySeq(TyTuple ts) -> List.forall scalar ts
            | TySeq e -> scalar e
            | t -> scalar t
        if f.Requires.IsEmpty || v.OverBudget || not (f.Params |> List.forall (fun p -> supported p.Ty)) then []
        else
            let found = ResizeArray<Eval.Value list>()
            let seen = HashSet<string>()
            let bounds = Array.ofList (constants @ [ -10I; 0I; 10I; 50I; 100I ])
            z3.SetTimeout(min 300 z3.DefaultTimeout)
            let lengths = [ 0 .. 6 ] @ (constants |> List.filter (fun c -> c > 6I && c <= 50I) |> List.map int) |> List.distinct
            for length in lengths do
                // a length the requires rules out (len(xs) >= 4) is not tried again
                let mutable feasible = true
                for attempt in 0 .. 11 do
                    if found.Count < 40 && feasible then
                        z3.Push()
                        let unknowns = ResizeArray<string * Ty>()
                        let fresh (t: Ty) =
                            let c = v.Fresh "in"
                            z3.Send("(declare-const " + c + (if t = TyBool then " Bool)" else " Int)"))
                            if t = TyNat then z3.Send("(assert (>= " + c + " 0))")
                            unknowns.Add((c, t))
                            BTerm c
                        let one (t: Ty) = match t with TyTuple ts -> BTup(List.map fresh ts) | t -> fresh t
                        let env =
                            f.Params
                            |> List.map (fun p -> p.Name, (match p.Ty with TySeq e -> BSeq [ for _ in 1 .. length -> one e ] | t -> one t))
                            |> Map.ofList
                        let mutable stated = false
                        for r in f.Requires do
                            try
                                z3.Send("(assert " + bterm (bexpr env r) + ")")
                                stated <- true
                            with Unbounded -> ()
                        // after the first try, random bounds: on each int parameter one time in two (a
                        // threshold t against the elements), and on one unknown of any kind
                        let bound (c: string) =
                            let b = if rnd.Next 2 = 0 then bounds.[rnd.Next bounds.Length] else bigint (rnd.Next(-100, 101))
                            z3.Send("(assert (" + (if rnd.Next 2 = 0 then ">=" else "<=") + " " + c + " " + bterm (BInt b) + "))")
                        let ints = unknowns |> Seq.filter (fun (_, t) -> t <> TyBool) |> Array.ofSeq
                        // and the edge cases of a threshold t against the elements of a sequence: t at an
                        // element (where `<` and `<=` differ), above all of them, below all of them
                        let elements =
                            f.Params |> List.collect (fun p ->
                                match env.[p.Name] with
                                | BSeq items -> items |> List.choose (fun x -> match x with BTerm c -> Some c | _ -> None)
                                | _ -> [])
                            |> Array.ofList
                        let against (c: string) (op: string) =
                            for x in elements do z3.Send("(assert (" + op + " " + c + " " + x + "))")
                        if attempt > 0 && ints.Length > 0 then
                            for p in f.Params do
                                match p.Ty, env.[p.Name] with
                                | (TyInt | TyNat), BTerm c when elements.Length > 0 && rnd.Next 2 = 0 ->
                                    match rnd.Next 3 with
                                    | 0 -> z3.Send("(assert (= " + c + " " + elements.[rnd.Next elements.Length] + "))")
                                    | 1 -> against c ">"
                                    | _ -> against c "<"
                                | (TyInt | TyNat), BTerm c when rnd.Next 2 = 0 -> bound c
                                | _ -> ()
                            bound (fst ints.[rnd.Next ints.Length])
                        // unknown too: the axioms of the program are quantified, so a model is only a candidate;
                        // the evaluator checks the requires on the input anyway
                        let answer = if stated then z3.Check() else Unsat
                        if attempt = 0 && answer = Unsat then feasible <- false
                        if answer <> Unsat then
                            let names = unknowns |> Seq.map fst |> List.ofSeq
                            let model =
                                List.zip (List.ofSeq unknowns) (z3.Values names)
                                |> List.choose (fun ((c, t), x) -> valueOf t x |> Option.map (fun value -> c, value))
                                |> Map.ofList
                            let rec value (b: BVal) : Eval.Value option =
                                match b with
                                | BTerm c -> model.TryFind c
                                | BInt n -> Some(Eval.VInt n)
                                | BBool x -> Some(Eval.VBool x)
                                | BSeq l -> l |> List.map value |> (fun vs -> if List.forall Option.isSome vs then Some(Eval.VSeq(List.map Option.get vs)) else None)
                                | BTup l -> l |> List.map value |> (fun vs -> if List.forall Option.isSome vs then Some(Eval.VTuple(List.map Option.get vs)) else None)
                            let input = f.Params |> List.map (fun p -> value env.[p.Name])
                            if input |> List.forall Option.isSome then
                                let values = input |> List.map Option.get
                                if seen.Add(String.Join("|", values |> List.map Eval.valueText)) then found.Add values
                        z3.Pop()
            z3.SetTimeout z3.DefaultTimeout
            List.ofSeq found

    member private v.RunConcreteOnThisThread(f: TFn) =
        let ev = Eval.Evaluator(fns, true)
        let plain = Eval.Evaluator(fns)
        let rnd = Random 7
        let names = f.Params |> List.map (fun p -> p.Name)
        let zero = f.Params |> List.map (fun p -> zeroValue p.Ty)
        let candidates =
            seq {
                yield zero
                // each constant of the program in each int parameter, the others zero
                for (k, p) in List.indexed f.Params do
                    match p.Ty with
                    | TyInt | TyNat ->
                        for c in constants do
                            if p.Ty = TyInt || c.Sign >= 0 then
                                yield zero |> List.mapi (fun i z -> if i = k then Eval.VInt c else z)
                    | _ -> ()
                for _ in 1 .. 4000 -> f.Params |> List.map (fun p -> inputValue rnd constants p.Ty)
            }
        let define = definedParams f plain
        let run (input: Eval.Value list) =
            concreteTries <- concreteTries + 1
            let env = define (List.zip names input |> Map.ofList)
            let values = names |> List.map (fun n -> env.[n])
            if f.Requires |> List.forall (fun r -> plain.Holds(r, env) = Some true) then
                concreteRuns <- concreteRuns + 1
                ev.ResetSteps()
                try ev.Run(f, values) |> ignore with
                | Eval.Violation(label, span) ->
                    if not (concrete.ContainsKey((label, span))) then
                        concrete.[(label, span)] <- List.zip names values |> List.map (fun (n, x) -> n, Eval.valueText x)
                | Eval.CannotEvaluate _ -> ()
        use e = candidates.GetEnumerator()
        while concreteRuns < 200 && e.MoveNext() do
            run e.Current
        // few random inputs satisfy the requires: ask the solver for some
        if concreteRuns < 20 then
            for input in v.SolverInputs(f, rnd) do
                run input
        // the branches of f that no valid run took, for the messages (at most three)
        if concreteRuns > 0 then
            untaken <-
                ifSpans f
                |> List.collect (fun sp ->
                    [ for outcome in [ true; false ] do
                        if not (ev.Taken.Contains((sp, outcome))) then
                            yield "the 'if' at line " + string sp.Start.Line + " (condition " + (if outcome then "true" else "false") + ")" ])
                |> List.truncate 3

    /// Check one obligation on the current path, report it if it fails, then assume it.
    member v.Check(st: State, o: Obligation) : State =
        match concrete.TryGetValue((o.Label, o.Span)) with
        | true, cex ->
            v.Report(o, "refuted", "cannot prove: " + o.Label + ": it fails when the function runs on the inputs below", cex, evidence = "run")
            { st with Assume = o.Goal :: st.Assume }
        | _ when v.OverBudget ->
            skippedHere <- skippedHere + 1
            skipped <- skipped + 1
            { st with Assume = o.Goal :: st.Assume }
        | _ ->
        z3.Push()
        for a in List.rev st.Assume do
            z3.Send("(assert " + a + ")")
        z3.Send("(assert (not " + o.Goal + "))")
        // an obligation about integers and booleans only, with all its facts: the second process
        // first (the same problem, without the axioms); otherwise as a second try
        // A try again (a fresh solver, or the second process) only after a quick "unknown", not
        // after a timeout: a hard obligation would pay its time limit twice. Within the budget.
        let retryLimit (first: CheckResult) =
            match first, v.Remaining with
            | Unknown "timeout", _ -> None
            | _, Some r when r <= 0 -> None
            | _, Some r -> Some(min r z3.DefaultTimeout)
            | _, None -> Some z3.DefaultTimeout
        beforeSolver (o.Label + ", solver, up to " + string ((min z3.DefaultTimeout (defaultArg v.Remaining Int32.MaxValue)) / 1000) + " s")
        let answer, isolatedCex =
            match v.Isolated(st, o, true) with
            | Some(r, cex) -> r, Some cex
            | None ->
                let first = v.BudgetedCheck(fun () -> z3.CheckBoth retryLimit)
                match first with
                | Unknown why when why <> "timeout" && not v.OverBudget ->
                    match v.Isolated(st, o, false) with
                    | Some(r, cex) -> r, Some cex
                    | None -> first, None
                | r -> r, None
        afterSolver ()
        match answer with
        | Unsat -> proved <- proved + 1
        | Sat when isolatedCex.IsSome -> v.ReportModel(o, isolatedCex.Value)
        // from the second process: no candidate model to read in the shared session
        | Unknown why when isolatedCex.IsSome ->
            let reason = if why = "timeout" then "timeout" else reasonText why
            v.Report(o, "inconclusive", "could not prove " + o.Label + (if why = "timeout" then " within the time limit" else "") + v.NoCounterexample(), [], reason = reason)
        | Sat -> v.ReportModel(o, v.CounterexampleValues())
        | Unknown "timeout" ->
            v.Report(o, "inconclusive", "could not prove " + o.Label + " within the time limit" + v.NoCounterexample(), [], reason = "timeout")
        | Unknown why ->
            // Quantifiers make Z3 incomplete: it stops with a candidate model it cannot confirm.
            // Shown as a *possible* counterexample: it often is the real one.
            let reason = reasonText why
            match v.Counterexample() with
            | [] -> v.Report(o, "inconclusive", "could not prove " + o.Label + v.NoCounterexample(), [], reason = reason)
            | cex ->
                v.Report(o, "inconclusive", "cannot prove: " + o.Label + " (possible counterexample, not confirmed by the solver)", cex,
                         reason = reason, evidence = "unconfirmed")
        z3.Pop()
        { st with Assume = o.Goal :: st.Assume }

    /// What the concrete runs say when the solver fails without a counterexample: facts only.
    /// No counterexample on small inputs does not show that the property holds (a bug at
    /// n == 1000, an input that a quantified requires makes rare), and an agent told "it may
    /// hold" adds asserts to prove a false property (external counter-review).
    member _.NoCounterexample() =
        if concreteTries = 0 then ""
        elif concreteRuns = 0 then
            " (the function was not run: none of the " + string concreteTries
            + " small inputs tried satisfies its requires, so there is no counterexample either way)"
        else
            " (no counterexample in " + string concreteRuns + " runs of the function on small inputs that satisfy its requires"
            + (if concreteRuns < 200 then ", out of " + string concreteTries + " tried" else "")
            + (if untaken.IsEmpty then "" else "; no run took " + String.Join(", ", untaken))
            + ": a bug may need other inputs; if the property holds, the proof needs a hint, an assert or a lemma)"

    /// The value of a term in the current model, as a Quod value. Sequences are axiomatized,
    /// so a sequence is read through its length and its elements (at most 50 of them).
    member v.ModelValue(term: string, t: Ty) : Eval.Value option =
        match t with
        | TySeq e ->
            match v.ModelValue("(" + seqOp "len" t + " " + term + ")", TyInt) with
            | Some(Eval.VInt n) when n.Sign >= 0 && n <= bigint 50 ->
                let items = [ for i in 0 .. int n - 1 -> v.ModelValue("(" + seqOp "nth" t + " " + term + " " + string i + ")", e) ]
                if items |> List.forall Option.isSome then Some(Eval.VSeq(items |> List.map Option.get)) else None
            | _ -> None
        | TyTuple ts ->
            let parts = ts |> List.mapi (fun k ct -> v.ModelValue("(" + tupleName ts + "_" + string k + " " + term + ")", ct))
            if parts |> List.forall Option.isSome then Some(Eval.VTuple(parts |> List.map Option.get)) else None
        | _ ->
            match z3.Values [ term ] with
            | [ x ] -> valueOf t x
            | _ -> None

    /// The parameters' values in the current model (empty when there is none).
    member v.CounterexampleValues() : (string * Eval.Value) list =
        let ps = paramsOf.[current.Value.Fn.Name]
        let values = ps |> List.map (fun (sym, ty) -> v.ModelValue(sym, ty))
        if values |> List.exists Option.isNone then []
        else List.zip ps values |> List.map (fun ((sym, _), value) -> sym.Substring(0, sym.IndexOf '@'), value.Value)

    member v.Counterexample() : (string * string) list =
        v.CounterexampleValues() |> List.map (fun (n, x) -> n, Eval.valueText x)

    /// Run the function on the solver's model, checking every obligation: does it break this one?
    /// Some true: yes, a certain counterexample; Some false: the run breaks nothing here (the
    /// model is a state the code does not reach, e.g. allowed by an invariant too weak to prove the
    /// obligation); None: the run could not tell (the model misses a parameter the run needs, or
    /// cannot be evaluated). Parameters the obligation is not about take their zero value.
    member v.Replay(o: Obligation, model: (string * Eval.Value) list) : bool option =
        let f = current.Value.Fn
        let values =
            f.Params |> List.map (fun p -> match List.tryFind (fun (n, _) -> n = p.Name) model with Some(_, x) -> x | None -> zeroValue p.Ty)
        let plain = Eval.Evaluator(fns)
        let env = List.zip (f.Params |> List.map (fun p -> p.Name)) values |> Map.ofList
        let fits = List.forall2 (fun (p: TParam) x -> plain.Fits(p.Ty, x)) f.Params values
        if not fits || model.IsEmpty then None
        elif not (f.Requires |> List.forall (fun r -> plain.Holds(r, env) = Some true)) then None
        else
            let ev = Eval.Evaluator(fns, true)
            Eval.withBigStack (fun () ->
                try
                    ev.Run(f, values) |> ignore
                    Some false
                with
                | Eval.Violation(label, span) -> Some(label = o.Label && span = o.Span)
                | Eval.CannotEvaluate _ -> None)

    /// A model of the negated obligation, confirmed by running the function on it (test of 0.1.2:
    /// the agent had to run quod_run itself to know whether the counterexample was real).
    member v.ReportModel(o: Obligation, model: (string * Eval.Value) list) =
        let text = model |> List.map (fun (n, x) -> n, Eval.valueText x)
        match v.Replay(o, model) with
        | Some true ->
            v.Report(o, "refuted", "cannot prove: " + o.Label + ": it fails when the function runs on the inputs below", text, evidence = "run")
        | Some false ->
            v.Report(o, "inconclusive",
                     "cannot prove: " + o.Label + ". The solver's counterexample below does not break it when the function runs on these inputs: "
                     + "the property may hold, and the proof needs a stronger invariant, an assert or a lemma", text, evidence = "unconfirmed")
        | None -> v.Report(o, "refuted", "cannot prove: " + o.Label, text, evidence = "solver")

    member v.Report(o: Obligation, status: string, message: string, cex: (string * string) list, ?reason: string, ?evidence: string) =
        diags.Add
            { File = file; Span = o.Span; Kind = "proof"; Status = status; Severity = Error
              Fn = Some current.Value.Fn.Name; Property = Some o.Label; Counterexample = cex
              Reason = reason; Evidence = (if cex.IsEmpty then None else evidence); Message = message }

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
        let constsIn (term: string) = constRx.Matches term |> Seq.map (fun m -> m.Value)
        let live = loop.Env |> Map.toSeq |> Seq.collect (snd >> constsIn) |> Set.ofSeq
        let paramNames = f.Params |> List.map (fun p -> p.Name) |> Set.ofList
        let roots =
            loop.Env |> Map.toSeq
            |> Seq.filter (fun (n, _) -> not (paramNames.Contains n) && not (List.contains n modified))
            |> Seq.collect (snd >> constsIn) |> Set.ofSeq
        loop <- { loop with Assume = relevantFacts live roots loop.Assume }
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
        v.RunConcrete f
        for r in f.Requires do
            st <- v.Assume(st, r) // its own obligations (well-formedness) are checked by Eval
        // Under an impossible precondition everything is "proved": reject it explicitly, or a
        // `requires false` would make any function verify (and look complete).
        if not f.Requires.IsEmpty && not v.OverBudget then
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
                      Reason = None; Evidence = None; Message = "the 'requires' clauses can never all hold, so this function could never be called and every proof about it would be empty" }
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
        v.ReportSkipped f
        current <- None
        concrete.Clear()
        concreteRuns <- 0
        z3.Pop()

    /// Declarations shared by all functions: tuple datatypes, statement functions (known by
    /// their contract only), and expression functions (known by their definition).
    member v.Prelude() =
        let tuples = ResizeArray<Ty list>()
        let elems = ResizeArray<Ty>()
        let rec visit (t: Ty) =
            match t with
            | TySeq e ->
                visit e
                if not (elems |> Seq.exists (fun x -> tySig x = tySig e)) then elems.Add e
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
        for e in elems do
            for line in seqAxioms e do z3.Send line
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
        v.RunConcrete f // a call that does not decrease (f(j - 0)) is found by running f
        let out = Collector()
        match f.Body with
        | TExprBody e -> v.Expr(e, env, [], out) |> ignore
        | TStmtBody _ -> ()
        let mutable st = { Env = env; Assume = List.rev (List.ofSeq out.Facts) @ List.rev (List.ofSeq silent.Facts) @ assume; Alive = true }
        for o in out.Obs |> Seq.filter (fun o -> o.Label.StartsWith "recursive call decreases") do
            st <- v.Check(st, o)
        // termination not proved for lack of time is not proved: the definition stays unknown
        // (a non-terminating definition would make every later proof vacuous)
        let unchecked = skippedHere > 0
        v.ReportSkipped f
        current <- None
        concrete.Clear()
        concreteRuns <- 0
        z3.Pop()
        diags.Count = before && not unchecked

    /// Completeness (pillar 5): can two different results satisfy the contract for the same
    /// valid input (or, with `loose`, two results that the declared relation does not allow)?
    /// unsat: determined. Otherwise the solver's candidate (input, r1, r2) is *evaluated* on
    /// concrete values: if the contract really accepts both, the function is underspecified
    /// (an error, with a certain witness); if not, the verdict is inconclusive (a warning).
    member v.Completeness(f: TFn) : bool =
        if v.OverBudget then
            diags.Add
                { File = file; Span = f.Span; Kind = "completeness"; Status = "not-attempted"; Severity = Warning
                  Fn = Some f.Name; Property = Some "the contract determines a unique result"; Counterexample = []
                  Reason = Some "budget"; Evidence = None
                  Message = "completeness not checked: the time budget of the check was used up (raise it with the budget argument of quod_check through MCP, --budget on the command line)" }
            false
        else
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
        // A loose relation that holds for any two values of the result type, without the ensures
        // (`loose (r1, r2) => true`), declares every result acceptable: the check below would then
        // prove nothing. A VerifBench agent wrote it to silence the check.
        match f.Loose with
        | Some l ->
            let rel = v.Expr(l.Relation, env.Add(l.Left, r1).Add(l.Right, r2), [], silent)
            z3.Push()
            for a in List.rev (List.ofSeq silent.Facts) @ List.rev assume do
                z3.Send("(assert " + a + ")")
            z3.Send("(assert (not " + rel + "))")
            z3.SetTimeout(min 1000 z3.DefaultTimeout)
            let total = z3.Check() = Unsat
            z3.SetTimeout z3.DefaultTimeout
            z3.Pop()
            // A relation whose every part concerns one result only (`a < len(xs) && b < len(xs)`)
            // relates nothing: it restates properties of each result, which the ensures already
            // give, so it accepts any two acceptable results as surely as `true` (first-user
            // test of 0.1.0). Testing it under the ensures would not do: any loose that passes
            // the completeness check holds under them, `(r1 == -1) == (r2 == -1)` included.
            let rec conjuncts (e: TExpr) =
                match e.Kind with
                | ELogic(OAnd, a, b) -> conjuncts a @ conjuncts b
                | _ -> [ e ]
            let relates (c: TExpr) = mentions l.Left c && mentions l.Right c
            let unrelated = not total && not (conjuncts l.Relation |> List.exists relates)
            if total || unrelated then
                diags.Add
                    { File = file; Span = f.Span; Kind = "completeness"; Status = "loose-accepts-all"; Severity = Warning
                      Fn = Some f.Name; Property = Some "the 'loose' relation restricts the results"
                      Counterexample = []
                      Reason = None; Evidence = None; Message =
                        (if total then "the 'loose' relation holds for any two results, whatever the ensures say"
                         else "the 'loose' relation does not relate the two results: each of its parts concerns one of them, so it accepts any two results the ensures accept")
                        + ": it declares every result acceptable, so the completeness check proves nothing. "
                        + "Say what two acceptable results have in common (for two indices of a maximum: xs[" + l.Left + "] == xs[" + l.Right + "]), or remove 'loose'" }
        | None -> ()
        for ens in f.Ensures do
            assume <- v.Expr(ens, env.Add("result", r1), [], silent) :: v.Expr(ens, env.Add("result", r2), [], silent) :: assume
        // An index result: the quantifiers of the ensures, instantiated at both results. "The
        // first maximum" (forall i in 0..result: xs[i] < xs[result]) is unique because each
        // result, as i, is below the other: the solver rarely picks these instances by itself
        // (first-user test of 0.1.0). Instances of what is assumed: nothing new is assumed.
        match f.Ret with
        | TyInt | TyNat ->
            // only where the result is an index (xs[result]) or a bound (0..result): elsewhere
            // (max_subarray: result is a sum) the instances are noise that hides the proof
            let rec indexed (e: TExpr) =
                match e.Kind with
                | EIndex(s, { Kind = EResult }) -> true
                | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> indexed a || indexed b
                | ESlice(a, b, c) -> indexed a || Option.exists indexed b || Option.exists indexed c
                | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a -> indexed a
                | EIf(a, b, c) | EQuant(_, _, a, b, c) -> indexed a || indexed b || indexed c
                | ESeq xs | ETuple xs | ECall(_, xs) -> List.exists indexed xs
                | EInt _ | EBool _ | EVar _ | EResult -> false
            let isResult (e: TExpr) = match e.Kind with EResult | EToNat { Kind = EResult } -> true | _ -> false
            let rec foralls (e: TExpr) =
                match e.Kind with
                | ELogic(OAnd, a, b) -> foralls a @ foralls b
                | EQuant(Syntax.Forall, name, lo, hi, body) when indexed body || isResult lo || isResult hi -> [ name, lo, hi, body ]
                | _ -> []
            for ens in f.Ensures do
                for (name, lo, hi, body) in foralls ens do
                    for result in [ r1; r2 ] do
                        for at in [ r1; r2 ] do
                            let en = env.Add("result", result)
                            let l, h = v.Expr(lo, en, [], silent), v.Expr(hi, en, [], silent)
                            let b = v.Expr(body, en.Add(name, at), [], silent)
                            assume <- ("(=> (and (<= " + l + " " + at + ") (< " + at + " " + h + ")) " + b + ")") :: assume
        | _ -> ()
        let goal =
            match f.Loose with
            | Some l -> v.Expr(l.Relation, env.Add(l.Left, r1).Add(l.Right, r2), [], silent)
            | None ->
                match f.Ret with
                | TySeq _ -> "(" + seqOp "eq" f.Ret + " " + r1 + " " + r2 + ")"
                | _ -> "(= " + r1 + " " + r2 + ")"
        for a in List.rev (List.ofSeq silent.Facts) @ List.rev assume do
            z3.Send("(assert " + a + ")")
        z3.Send("(assert (not " + goal + "))")
        let answer = v.BudgetedCheck z3.Check
        let candidate () =
            let terms = (ps |> List.ofSeq) @ [ r1, f.Ret; r2, f.Ret ]
            let parsed = terms |> List.map (fun (term, ty) -> v.ModelValue(term, ty))
            if parsed |> List.forall Option.isSome then Some(parsed |> List.map Option.get) else None
        let report (status: string) (severity: Severity) (message: string) (witness: (string * string) list) =
            diags.Add
                { File = file; Span = f.Span; Kind = "completeness"; Status = status; Severity = severity
                  Fn = Some f.Name; Property = Some "the contract determines a unique result"
                  Counterexample = witness; Reason = None; Evidence = None; Message = message }
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
        /// When Z3 gives no usable model (sequences are axiomatized: a formula with no concrete
        /// sequence term is often "unknown"), search concretely: small inputs that satisfy the
        /// requires, small candidate results (and the parameters of the result type), checked
        /// against the ensures by the evaluator. Two accepted results are a confirmed witness.
        let concrete () : (string * string) list option =
            let rnd = Random 5
            let ev = Eval.Evaluator(fns)
            let mutable found = None
            let mutable tries = 0
            let mutable inputs = 0
            while found.IsNone && tries < 3000 && inputs < 60 do
                tries <- tries + 1
                let values = f.Params |> List.map (fun p -> randomValue rnd p.Ty)
                let env = List.zip (f.Params |> List.map (fun p -> p.Name)) values |> Map.ofList
                if f.Requires |> List.forall (fun r -> ev.Holds(r, env) = Some true) then
                    inputs <- inputs + 1
                    let sameType = List.zip f.Params values |> List.filter (fun (p, _) -> p.Ty = f.Ret) |> List.map snd
                    let accepted =
                        (sameType @ smallValues f.Ret)
                        |> List.distinct
                        |> List.filter (fun r -> ev.Fits(f.Ret, r) && f.Ensures |> List.forall (fun e -> ev.Holds(e, env.Add("result", r)) = Some true))
                    found <-
                        [ for a in accepted do for b in accepted -> a, b ]
                        |> List.tryPick (fun (a, b) -> if a = b then None else confirm (values @ [ a; b ]))
            found
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
                    match w with
                    | Some _ -> w
                    | None -> Eval.withBigStack concrete
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
                report "inconclusive" Warning ("completeness not decided: the solver found neither two results the contract accepts nor a proof that they are equal (the contract may well be complete). "
                        + "Try to find two different results it accepts on a small input; if there are none, state the result more directly: for an index, what holds before it and at it") []
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
      WithContract: int
      Lemmas: int
      /// Proof obligations not sent to the solver: the time budget was used up
      NotAttempted: int }

/// Verify every function of a well-typed program with one Z3 session:
/// 1. declarations; definitions of the non-recursive expression functions;
/// 2. termination of the recursive expression functions, without their definitions;
/// 3. definitions of those that terminate;
/// 4. every function, with all the definitions that are safe to know.
/// Within a time budget (seconds, 0: none), functions in the order of the file.
let rec verify (file: string) (prog: TProgram) (z3: Session) (budgetSeconds: int) : VerifyResult =
    verifyWith file prog z3 budgetSeconds (fun _ _ _ -> ())

/// The same, telling `progress done total what` as it goes (`quod mcp` sends it on as MCP progress
/// notifications): when it starts and ends each function and each completeness check, and when a
/// try of the solver has run for a second (a quick one is not told). `done` grows at each call (MCP
/// asks it): k + 1 when the k-th step (0-based) ends, between k and k + 1 while it runs (test of
/// 0.1.2: notifications only at the end of each function told nothing during a long one).
and verifyWith (file: string) (prog: TProgram) (z3: Session) (budgetSeconds: int) (progress: float -> int -> string -> unit) : VerifyResult =
    let v = Verifier(file, prog, z3, budgetSeconds * 1000)
    let mutable step = 0
    let mutable within = 0
    let mutable stepName = ""
    let clock = Diagnostics.Stopwatch.StartNew()
    let mutable lastTold = -1000L
    let mutable total = 0
    let gate = obj ()
    let tell (what: string) =
        lock gate (fun () ->
            within <- within + 1
            lastTold <- clock.ElapsedMilliseconds
            progress (float step + 1.0 - 1.0 / float (within + 1)) total what)
    let start (what: string) (name: string) =
        lock gate (fun () ->
            within <- 0
            stepName <- name)
        tell what
    let finish (what: string) =
        lock gate (fun () ->
            step <- step + 1
            lastTold <- clock.ElapsedMilliseconds
            progress (float step) total what)
    // a try of the solver still running after a second is told, once
    let mutable running: (string * int64) option = None
    v.BeforeSolver <- (fun what -> lock gate (fun () -> running <- Some(stepName + ": " + what, clock.ElapsedMilliseconds)))
    v.AfterSolver <- (fun () -> lock gate (fun () -> running <- None))
    use _watch =
        new Threading.Timer(
            (fun _ ->
                let due = lock gate (fun () ->
                    match running with
                    | Some(what, t) when clock.ElapsedMilliseconds - t >= 1000L ->
                        running <- None
                        Some what
                    | _ -> None)
                due |> Option.iter tell),
            null, 250, 250)
    z3.Init()
    v.Prelude()
    let exprFns = prog.Fns |> List.filter (fun f -> f.IsExprFn)
    for f in exprFns |> List.filter (fun f -> not f.IsRecursive) do
        v.Define f
    let recursive = exprFns |> List.filter (fun f -> f.IsRecursive)
    let terminating = recursive |> List.filter (fun f -> f.Decreases.IsSome && v.Termination f)
    for f in terminating do
        v.Define f
    let withContract = prog.Fns |> List.filter (fun f -> not f.Ensures.IsEmpty && not f.IsLemma)
    total <- prog.Fns.Length + withContract.Length
    for f in prog.Fns do
        start ("checking the obligations of " + f.Name) f.Name
        v.Function f
        finish ("checked the obligations of " + f.Name)
    v.Close()
    // a lemma has no result to determine: it is a proof, its ensures are what it proves
    let determined =
        withContract
        |> List.filter (fun f ->
            start ("checking the completeness of " + f.Name) f.Name
            let d = v.Completeness f
            finish ("checked the completeness of " + f.Name)
            d)
        |> List.length
    { Diagnostics = v.Diagnostics; Proved = v.Proved; Determined = determined; WithContract = withContract.Length
      Lemmas = prog.Fns |> List.filter (fun f -> f.IsLemma) |> List.length; NotAttempted = v.NotAttempted }
