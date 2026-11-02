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

let styleOf (fnNames: Set<string>) (f: TFn) : Style option =
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
        if not f.IsExprFn && f.Ret = TyBool && alwaysTrue then Some LemmaAsFunction
        elif cs |> List.exists (fun c -> compound c && bodyKeys.Contains(key c)) then Some Restated
        elif cs |> List.exists (fun c -> match c.Kind with ECall(g, _) -> fnNames.Contains g | _ -> false) then Some Model
        else Some Properties

/// One diagnostic per classified function: a note for properties and models, a warning for a
/// restated body or a missing contract.
let diagnostics (file: string) (prog: TProgram) : Diagnostic list =
    let names = prog.Fns |> List.map (fun f -> f.Name) |> Set.ofList
    prog.Fns
    |> List.choose (fun f ->
        styleOf names f
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
    | ESeq xs | ETuple xs -> List.collect calls xs
    | EIndex(a, b) | EConcat(a, b) | EArith(_, a, b) | ECmp(_, a, b) | EEq(a, b) | ELogic(_, a, b) -> calls a @ calls b
    | ESlice(a, b, c) -> calls a @ (Option.toList b |> List.collect calls) @ (Option.toList c |> List.collect calls)
    | EProj(a, _) | ELen a | ENeg a | ENot a | EToNat a -> calls a
    | EIf(a, b, c) | EQuant(_, _, a, b, c) -> calls a @ calls b @ calls c
    | EInt _ | EBool _ | EVar _ | EResult -> []

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
