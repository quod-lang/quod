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
module Quod.ContractStyle

open Quod.Typed
open Quod.Diagnostics

type Style =
    | Properties
    | Model
    | Restated
    | NoContract

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
    if f.Ensures.IsEmpty then (if f.IsExprFn then None else Some NoContract)
    else
        let values =
            match f.Body with
            | TExprBody e -> leaves e
            | TStmtBody ss -> returned ss
        let bodyKeys = values |> List.map key |> Set.ofList
        let cs = f.Ensures |> List.collect claims
        if cs |> List.exists (fun c -> compound c && bodyKeys.Contains(key c)) then Some Restated
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
            { File = file; Span = f.Span; Kind = "contract"; Status = status; Severity = severity
              Fn = Some f.Name; Property = Some "contract style"; Counterexample = []; Message = message }))
