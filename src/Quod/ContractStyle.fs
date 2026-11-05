/// The style of each contract: how its ensures define the result. The completeness check makes
/// a contract determine the result; it cannot tell *how*. The shortest determined contract is
/// `ensures result == <the body>`, and agents write it (VerifBench run quod1, rotate): the proof
/// then shows little more than the absence of errors. So every contract is classified, for the
/// report and its reviewers, and a restated body is a warning.
///
/// - properties: what the result is (bounds, order, membership...), not how to compute it;
/// - model: `result == f(...)` with f a function of the program, a model or reference
///   implementation, proved to compute the same thing as the code: the model is what to review;
/// - restated: `result == e` where e is, word for word, a value the body returns;
/// - none: a statement function without ensures (a warning). Its callers know it by its contract
///   only, so they know nothing, and nothing is proved about its result. An expression function
///   without ensures is not classified: the verifier knows its definition. (A Haiku agent's
///   rle_encode, VerifBench run quod2-haiku, had no ensures at all and passed the check.)
/// - a lemma written as a function (a warning): a statement function that returns `true` on every
///   path, its ensures being the facts it proves. It verifies, but it is generated and run: a
///   recursive one made the external review's range_sum O(n), and fail at n = 5000. `lemma`
///   says the same and is erased.
module Quod.ContractStyle

open System.Collections.Generic
open Quod.Typed
open Quod.Diagnostics

type Style =
    | Properties
    | Model
    | Restated
    | NoContract
    | LemmaAsFunction

/// An expression as text, whatever its positions: two expressions with the same key are the same.
let private key (e: TExpr) = Printer.exprText (toSyntax e)

/// The values an expression body returns: the branches of its ifs.
let rec private leaves (e: TExpr) : TExpr list =
    match e.Kind with
    | EIf(_, a, b) -> leaves a @ leaves b
    | EToNat x -> leaves x
    | _ -> [ e ]

/// The values a statement body returns.
let rec private returned (body: TStmt list) : TExpr list =
    body
    |> List.collect (fun s ->
        match s.Kind with
        | SReturn e -> leaves e
        | SIf(_, a, b) -> returned a @ returned b
        | SWhile(_, _, _, b) -> returned b
        | _ -> [])

/// What an ensures says the result is equal to: `result == e`, possibly under guards
/// (`c ==> result == e`) or in a conjunction.
let rec private claims (e: TExpr) : TExpr list =
    match e.Kind with
    | ELogic(OImplies, _, b) -> claims b
    | ELogic(OAnd, a, b) -> claims a @ claims b
    | EEq({ Kind = EResult }, v)
    | EEq(v, { Kind = EResult }) -> [ v ]
    | _ -> []

/// A variable or a literal is no restatement: `ensures len(xs) == 0 ==> result == xs`.
let rec private compound (e: TExpr) =
    match e.Kind with
    | EVar _ | EInt _ | EBool _ | EResult -> false
    | EToNat x -> compound x
    | _ -> true

/// The functions whose value the program uses. A call that only binds a variable which is never
/// read, or only returned by the function itself (`let ih = f(...); return ih;` in f, the old
/// lemma idiom), does not count. `if feature_enabled() { ... }` does: such a function cannot
/// become a lemma, which has no value (external counter-review).
let valueUses (prog: TProgram) : Set<string> =
    let used = HashSet<string>()
    let rec expr (e: TExpr) =
        match e.Kind with
        | ECall(g, xs) -> used.Add g |> ignore; List.iter expr xs
        | ESeq xs | ETuple xs | ECons(_, xs) -> List.iter expr xs
        | EField(a, _, _) -> expr a
        | EMatch(a, arms) -> expr a; arms |> List.iter (fun (_, _, b) -> expr b)
        | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> expr a; expr b
        | ESlice(a, b, c) -> expr a; Option.iter expr b; Option.iter expr c
        | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a | EConvert a -> expr a
        | EIf(a, b, c) | EQuant(_, _, a, b, c) -> expr a; expr b; expr c
        | EInt _ | EBool _ | EVar _ | EResult -> ()
    /// Does a variable named n appear in e?
    let rec reads (n: string) (e: TExpr) =
        match e.Kind with
        | EVar m -> m = n
        | ECall(_, xs) | ESeq xs | ETuple xs | ECons(_, xs) -> List.exists (reads n) xs
        | EField(a, _, _) -> reads n a
        | EMatch(a, arms) -> reads n a || arms |> List.exists (fun (_, _, b) -> reads n b)
        | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> reads n a || reads n b
        | ESlice(a, b, c) -> reads n a || Option.exists (reads n) b || Option.exists (reads n) c
        | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a | EConvert a -> reads n a
        | EIf(a, b, c) | EQuant(_, _, a, b, c) -> reads n a || reads n b || reads n c
        | EInt _ | EBool _ | EResult -> false
    for f in prog.Fns do
        match f.Body with
        | TExprBody e -> expr e
        | TStmtBody body ->
            // calls bound by `let x = g(...)`, then judged by the uses of x
            let bound = ResizeArray<string * string>()
            let rec stmt (st: TStmt) =
                match st.Kind with
                | SLet(_, x, _, { Kind = ECall(g, args) }) when not (isLemmaBinding x) ->
                    bound.Add((x, g))
                    List.iter expr args
                | SLet(_, _, _, e) | SAssign(_, e) | SAssert e | SReturn e -> expr e
                | SIf(c, a, b) -> expr c; List.iter stmt a; List.iter stmt b
                | SWhile(c, invs, d, b) -> expr c; List.iter expr invs; expr d; List.iter stmt b
            List.iter stmt body
            let rec readers (x: string) (g: string) (st: TStmt) =
                match st.Kind with
                | SReturn { Kind = EVar m } when m = x && g = f.Name -> false // the recursive idiom
                | SLet(_, _, _, e) | SAssign(_, e) | SAssert e | SReturn e -> reads x e
                | SIf(c, a, b) -> reads x c || List.exists (readers x g) a || List.exists (readers x g) b
                | SWhile(c, invs, d, b) -> reads x c || List.exists (reads x) invs || reads x d || List.exists (readers x g) b
            for (x, g) in bound do
                if body |> List.exists (readers x g) then used.Add g |> ignore
    Set.ofSeq used

/// An expression with its variables replaced, and the calls to `g` as calls to `f`: a model `g`
/// of `f`, unfolded once where `f` is, reads as the body of `f` when it copies it.
let rec private unfold (values: Map<string, TExpr>) (g: string) (f: string) (e: TExpr) : TExpr =
    let go = unfold values g f
    let kind =
        match e.Kind with
        | EVar n when values.ContainsKey n -> values.[n].Kind
        | EInt _ | EBool _ | EVar _ | EResult -> e.Kind
        | ESeq xs -> ESeq(List.map go xs)
        | ETuple xs -> ETuple(List.map go xs)
        | EIndex(a, b) -> EIndex(go a, go b)
        | ESlice(a, b, c) -> ESlice(go a, Option.map go b, Option.map go c)
        | EProj(a, k) -> EProj(go a, k)
        | ECons(k, xs) -> ECons(k, List.map go xs)
        | EField(a, k, i) -> EField(go a, k, i)
        | EMatch(a, arms) -> EMatch(go a, arms |> List.map (fun (k, n, b) -> k, n, go b))
        | ELen a -> ELen(go a)
        | EConvert a -> EConvert(go a)
        | ECall(h, xs) -> ECall((if h = g then f else h), List.map go xs)
        | ENeg a -> ENeg(go a)
        | ENot a -> ENot(go a)
        | EArith(o, a, b) -> EArith(o, go a, go b)
        | EConcat(a, b) -> EConcat(go a, go b)
        | ECmp(o, a, b) -> ECmp(o, go a, go b)
        | EEq(a, b) -> EEq(go a, go b)
        | ELogic(o, a, b) -> ELogic(o, go a, go b)
        | EIf(a, b, c) -> EIf(go a, go b, go c)
        | EQuant(q, v, lo, hi, b) -> EQuant(q, v, go lo, go hi, go b)
        | EToNat a -> EToNat(go a)
    { e with Kind = kind }

let styleOf (fns: Map<string, TFn>) (usedAsValue: Set<string>) (f: TFn) : Style option =
    if f.IsLemma then None // a proof, not a function: its ensures are what it proves
    elif f.Ensures.IsEmpty then (if f.IsExprFn then None else Some NoContract)
    else
        let values =
            match f.Body with
            | TExprBody e -> leaves e
            | TStmtBody ss -> returned ss
        // returns true on every path, or says so: `ensures result` (the idiom returns `ih`)
        let alwaysTrue =
            values |> List.forall (fun v -> match v.Kind with EBool true -> true | _ -> false)
            || f.Ensures |> List.exists (fun e -> match e.Kind with EResult -> true | _ -> false)
        let bodyKeys = values |> List.map key |> Set.ofList
        let cs = f.Ensures |> List.collect claims
        if not f.IsExprFn && f.Ret = TyBool && alwaysTrue && not (usedAsValue.Contains f.Name) then Some LemmaAsFunction
        elif cs |> List.exists (fun c -> compound c && bodyKeys.Contains(key c)) then Some Restated
        // `result == copy(x)`, where `copy` is written as the body is (review of 0.1.4)
        elif cs |> List.exists (fun c ->
                match c.Kind with
                | ECall(g, args) when g <> f.Name ->
                    match fns.TryFind g with
                    | Some { Body = TExprBody body; Params = ps } when ps.Length = args.Length ->
                        let values = List.map2 (fun (p: TParam) a -> p.Name, a) ps args |> Map.ofList
                        let copied = leaves (unfold values g f.Name body)
                        copied |> List.exists compound && copied |> List.forall (fun x -> bodyKeys.Contains(key x))
                    | _ -> false
                | _ -> false) then Some Restated
        elif cs |> List.exists (fun c -> match c.Kind with ECall(g, _) -> fns.ContainsKey g | _ -> false) then Some Model
        else Some Properties

/// One diagnostic per classified function: a note for properties and models, a warning for a
/// restated body or a missing contract.
let diagnostics (file: string) (prog: TProgram) : Diagnostic list =
    let fns = prog.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList
    let uses = valueUses prog
    prog.Fns
    |> List.choose (fun f ->
        styleOf fns uses f
        |> Option.map (fun style ->
            let status, severity, message =
                match style with
                | Properties -> "properties", Info, "the contract states properties of the result"
                | Model ->
                    "model", Info,
                    "the contract defines the result by a function of the program: the proof shows that the code computes what this model computes, so the model is what to review"
                | Restated ->
                    "restated", Warning,
                    "the ensures restates what the body returns: the proof shows little more than the absence of errors. State properties of the result, or define it by a simpler model (a small formula that is its own specification can stay as it is)"
                | NoContract ->
                    "none", Warning,
                    "no ensures: nothing is proved about the result, and callers know nothing about it (a function with statements is known by its contract only). State what the result is"
                | LemmaAsFunction ->
                    "lemma-as-function", Warning,
                    "'" + f.Name + "' always returns true and states facts in its ensures: it is a lemma written as a function, so the generated code runs it at every call (a recursive one costs its depth, and can overflow the stack). Write it 'lemma " + f.Name + "(...)', without result type and 'ensures result', and call it as a statement, '" + f.Name + "(...);': it is then erased"
            { File = file; Span = f.Span; Kind = "contract"; Status = status; Severity = severity
              Fn = Some f.Name; Property = Some "contract style"; Counterexample = []; Reason = None; Evidence = None; Message = message }))

/// The functions called in an expression.
let rec private calls (e: TExpr) : string list =
    match e.Kind with
    | ECall(g, args) -> g :: List.collect calls args
    | ESeq xs | ETuple xs | ECons(_, xs) -> List.collect calls xs
    | EField(a, _, _) -> calls a
    | EMatch(a, arms) -> calls a @ (arms |> List.collect (fun (_, _, b) -> calls b))
    | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> calls a @ calls b
    | ESlice(a, b, c) -> calls a @ (Option.toList b |> List.collect calls) @ (Option.toList c |> List.collect calls)
    | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a | EConvert a -> calls a
    | EIf(a, b, c) | EQuant(_, _, a, b, c) -> calls a @ calls b @ calls c
    | EInt _ | EBool _ | EVar _ | EResult -> []

let rec private callsIn (items: TStmt list) : string list =
    items |> List.collect (fun s ->
        match s.Kind with
        | SLet(_, _, _, e) | SAssign(_, e) | SAssert e | SReturn e -> calls e
        | SIf(c, a, b) -> calls c @ callsIn a @ callsIn b
        | SWhile(c, invs, _, b) -> calls c @ List.collect calls invs @ callsIn b)

/// What must be refused before any proof. A `run_by` function that reaches the function it runs for
/// would loop for ever, though each is proved. A contract that speaks of its own function says nothing
/// of it, and the solver's definition of it would loop.
let beforeProofs (file: string) (prog: TProgram) : Diagnostic list =
    let byName = prog.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList
    let bodyCalls (f: TFn) =
        match f.Body with
        | TExprBody e -> (if f.RunBy.IsSome then [] else calls e) @ Option.toList f.RunBy
        | TStmtBody items -> callsIn items
    let rec reaches (seen: Set<string>) (target: string) (from: string) =
        from = target
        || (not (seen.Contains from)
            && (match byName.TryFind from with
                | Some f -> bodyCalls f |> List.exists (reaches (seen.Add from) target)
                | None -> false))
    let error (f: TFn) (message: string) : Diagnostic =
        { File = file; Span = f.Span; Kind = "type"; Status = "error"; Severity = Error; Fn = Some f.Name
          Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }
    [ for f in prog.Fns do
          if f.Ensures @ f.Requires |> List.collect calls |> List.contains f.Name then
              yield error f ("the contract of '" + f.Name + "' mentions '" + f.Name + "': a contract says what a function does in other terms")
          match f.RunBy with
          | Some g when reaches Set.empty f.Name g ->
              yield error f ("'run_by " + g + "': it calls '" + f.Name + "' back, so the generated code would loop for ever")
          | _ -> () ]

/// The property of a review note, followed by the functions whose contracts use the model.
let reviewProperty = "used by the contracts of "

/// What a reviewer must read besides the proofs, as notes:
/// - each `loose`: the freedom it declares is accepted as stated, the proof cannot tell whether
///   it is intended;
/// - each function the contracts are stated with (directly, or through the expression functions
///   they call): a determined contract can still describe the wrong function, and a model is
///   only as right as its definition.
let review (file: string) (prog: TProgram) : Diagnostic list =
    let byName = prog.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList
    let note (f: TFn) kind status property message =
        { File = file; Span = f.Span; Kind = kind; Status = status; Severity = Info; Fn = Some f.Name
          Property = Some property; Counterexample = []; Reason = None; Evidence = None; Message = message }
    let looseNotes =
        prog.Fns |> List.choose (fun f ->
            f.Loose |> Option.map (fun l ->
                note f "loose" "declared" "declared freedom"
                    ("the contract accepts any two results related by 'loose (" + l.Left + ", " + l.Right + ") => "
                     + Printer.exprText (toSyntax l.Relation) + "': check that this freedom is intended")))
    // the functions a contract relies on, through the bodies of expression functions
    let rec closure (seen: Set<string>) (todo: string list) =
        match todo with
        | [] -> seen
        | g :: rest when seen.Contains g || not (byName.ContainsKey g) -> closure seen rest
        | g :: rest ->
            let inner = match byName.[g].Body with TExprBody b -> calls b | TStmtBody _ -> []
            closure (seen.Add g) (inner @ rest)
    let users =
        prog.Fns
        |> List.filter (fun f -> not f.IsLemma && not f.Ensures.IsEmpty)
        |> List.collect (fun f ->
            let direct = (f.Ensures |> List.collect calls) @ (f.Loose |> Option.toList |> List.collect (fun l -> calls l.Relation))
            closure Set.empty direct |> Set.remove f.Name |> Set.toList |> List.map (fun g -> g, f.Name))
    let reviewNotes =
        prog.Fns |> List.choose (fun g ->
            match users |> List.filter (fun (m, _) -> m = g.Name) |> List.map snd with
            | [] -> None
            | fs ->
                Some(
                    note g "review" "model" (reviewProperty + String.concat ", " fs)
                        ("the contracts of " + String.concat ", " fs + " are stated with '" + g.Name
                         + "': the proofs show that the code agrees with it, not that it says what was meant, so read it")))
    looseNotes @ reviewNotes

/// The functions a function calls: in its contract, its hints and its body.
let private callees (f: TFn) : string list =
    let rec stmt (s: TStmt) =
        match s.Kind with
        | SLet(_, _, _, e) | SAssign(_, e) | SAssert e | SReturn e -> calls e
        | SIf(c, a, b) -> calls c @ List.collect stmt a @ List.collect stmt b
        | SWhile(c, invs, d, b) -> calls c @ List.collect calls invs @ calls d @ List.collect stmt b
    (f.Requires @ f.Ensures @ Option.toList f.Decreases |> List.collect calls)
    @ (f.Loose |> Option.toList |> List.collect (fun l -> calls l.Relation))
    @ (match f.Body with
       | TExprBody e -> calls e
       | TStmtBody body -> List.collect stmt body)

/// `--require-contracts`: a function without a contract is an error, so a verdict of `verified`
/// means that something was proved about the result. (VerifBench run t6-qwen3-30b: 6 of the 8
/// files accepted had no ensures at all, and a warning did not stop the agent.) An expression
/// function no other function calls is covered too: it is not a helper its definition explains,
/// but a result nothing is stated about. So is a `loose` that accepts every result, the same hole
/// under another name (run t6-qwen3-30b-strict, rle_encode: `loose (r1, r2) => true`), and a lemma
/// written as a function, whose `ensures result` says nothing about a result (review of 0.1.4).
/// `found` is every diagnostic of the check, the styles included.
let required (file: string) (prog: TProgram) (found: Diagnostic list) : Diagnostic list =
    let message = "no ensures, and --require-contracts asks for a contract: nothing is proved about the result. State what the result is"
    let raised =
        found
        |> List.map (fun d ->
            if d.Kind = "contract" && d.Status = "none" then { d with Severity = Error; Message = message }
            elif d.Kind = "completeness" && d.Status = "loose-accepts-all" then { d with Severity = Error }
            elif d.Kind = "contract" && d.Status = "lemma-as-function" then { d with Severity = Error }
            else d)
    let called = prog.Fns |> List.collect (fun f -> callees f |> List.filter (fun g -> g <> f.Name)) |> Set.ofList
    let entries =
        prog.Fns
        |> List.filter (fun f -> not f.IsLemma && f.IsExprFn && f.Ensures.IsEmpty && not (called.Contains f.Name))
        |> List.map (fun f ->
            { File = file; Span = f.Span; Kind = "contract"; Status = "none"; Severity = Error
              Fn = Some f.Name; Property = Some "contract style"; Counterexample = []; Reason = None; Evidence = None; Message = message })
    raised @ entries
