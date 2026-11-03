/// The stages of `quod check` and `quod build`, without any output: shared by the command line
/// and the MCP server, which present the same results differently.
module Quod.Pipeline

open System
open System.IO
open Quod.Diagnostics

type Settings =
    { Z3: string option
      /// Seconds per proof obligation
      Timeout: int
      /// Seconds for the whole check (0: none)
      Budget: int
      SmtLog: string option
      /// Stops the check: z3 is killed, and check ends with Failure "cancelled" (quod mcp)
      Cancel: Threading.CancellationToken
      /// Told `done total what` as the check goes on (quod mcp: progress notifications)
      Progress: float -> int -> string -> unit }

let defaultSettings =
    { Z3 = None; Timeout = 10; Budget = 300; SmtLog = None; Cancel = Threading.CancellationToken.None; Progress = fun _ _ _ -> () }

/// What checking a file gives.
type Outcome =
    /// Parsed and well-typed: the verification result (it may still have errors).
    | Checked of Typed.TProgram * Vcgen.VerifyResult
    /// A syntax error or type errors: nothing was proved.
    | Rejected of Diagnostic list
    /// Something outside the program: z3 missing, or z3 failing.
    | Failure of message: string * exitCode: int

/// Parse, type-check, prove and check completeness.
let check (file: string) (src: string) (s: Settings) : Outcome =
    try
        let program = Parser.parseProgram file src
        let typed, typeErrors = Typecheck.check file program
        if not typeErrors.IsEmpty then Rejected typeErrors
        else
            match Smt.findZ3 s.Z3 with
            | None -> Failure("z3 not found; put it next to quod, set QUOD_Z3, or pass --z3 PATH", 2)
            | Some z3Path ->
                use logWriter = (match s.SmtLog with Some p -> new StreamWriter(p) | None -> null)
                let log = if isNull logWriter then None else Some(logWriter :> TextWriter)
                use session = new Smt.Session(z3Path, s.Timeout * 1000, log, s.Cancel)
                let verified = Vcgen.verifyWith file typed session s.Budget s.Progress
                Checked(typed, { verified with Diagnostics = verified.Diagnostics @ ContractStyle.diagnostics file typed @ ContractStyle.review file typed })
    with
    | QuodError d -> Rejected [ d ]
    | Smt.SmtFailure message -> Failure("internal error while talking to z3: " + message, 3)

let errorsOf (r: Vcgen.VerifyResult) = r.Diagnostics |> List.filter (fun d -> d.Severity = Error)

let rec summary (r: Vcgen.VerifyResult) =
    let errors = errorsOf r
    let proofErrors = errors |> List.filter (fun d -> d.Kind = "proof" && d.Status <> "not-attempted") |> List.length
    let underspecified = errors |> List.filter (fun d -> d.Kind = "completeness") |> List.length
    string r.Proved + " proof obligation(s) proved"
    + (if proofErrors > 0 then ", " + string proofErrors + " failed" else "")
    + (if r.NotAttempted > 0 then ", " + string r.NotAttempted + " not attempted (time budget used up)" else "")
    + "; " + string r.Determined + " of " + string r.WithContract + " contract(s) determine their result"
    + (if underspecified > 0 then ", " + string underspecified + " underspecified" else "")
    + styleSummary r
    + (if r.Lemmas > 0 then "; " + string r.Lemmas + " lemma(s)" else "")
    + reviewSummary r

/// "; loose: binary_search; to review with the contracts: sum (prefix_sums, range_sum)": what
/// the proofs cannot vouch for, a reviewer reads.
and private reviewSummary (r: Vcgen.VerifyResult) =
    let names kind = r.Diagnostics |> List.filter (fun d -> d.Kind = kind) |> List.choose (fun d -> d.Fn)
    let loose = names "loose"
    let models =
        r.Diagnostics
        |> List.filter (fun d -> d.Kind = "review")
        |> List.map (fun d -> d.Fn.Value + " (" + d.Property.Value.Substring(ContractStyle.reviewProperty.Length) + ")")
    (if loose.IsEmpty then "" else "; loose: " + String.Join(", ", loose))
    + (if models.IsEmpty then "" else "; to review with the contracts: " + String.Join(", ", models))

/// "; contracts: 2 by properties, 1 by a model, 1 restating the body, 1 missing" (the styles present).
and private styleSummary (r: Vcgen.VerifyResult) =
    let count status = r.Diagnostics |> List.filter (fun d -> d.Kind = "contract" && d.Status = status) |> List.length
    let parts =
        [ count "properties", " by properties"; count "model", " by a model"; count "restated", " restating the body"
          count "none", " missing (no ensures)"; count "lemma-as-function", " lemma written as a function" ]
        |> List.filter (fun (n, _) -> n > 0)
        |> List.map (fun (n, text) -> string n + text)
    if parts.IsEmpty then "" else "; contracts: " + String.Join(", ", parts)

/// What `build` does with a checked program: the generated code, with the functions whose
/// contracts are checked at run time (--runtime-checks), or why it is not built.
let generate (file: string) (typed: Typed.TProgram) (r: Vcgen.VerifyResult) (runtimeChecks: bool) : Result<string * Set<string>, string> =
    let errors = errorsOf r
    let unproved = errors |> List.filter (fun d -> d.Kind = "proof") |> List.choose (fun d -> d.Fn) |> Set.ofList
    if errors |> List.exists (fun d -> d.Kind = "completeness") then
        Result.Error "not built: an underspecified contract cannot be compiled (fix it, or declare the freedom with 'loose')"
    elif not unproved.IsEmpty && not runtimeChecks then
        Result.Error("not built: " + summary r + ". Fix the proofs, or build with --runtime-checks")
    else
        Ok(CodegenPython.generate file typed unproved, unproved)
