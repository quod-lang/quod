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
      /// A function without a contract is an error (--require-contracts)
      RequireContracts: bool
      SmtLog: string option
      /// Stops the check: z3 is killed, and check ends with Failure "cancelled" (quod mcp)
      Cancel: Threading.CancellationToken
      /// Told `done total what` as the check goes on (quod mcp: progress notifications)
      Progress: float -> int -> string -> unit }

let defaultSettings =
    { Z3 = None; Timeout = 10; Budget = 300; RequireContracts = false; SmtLog = None; Cancel = Threading.CancellationToken.None; Progress = fun _ _ _ -> () }

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
        match Modules.load file src with
        | Result.Error ds -> Rejected ds
        | Ok loaded ->
        let inFiles = List.map (Modules.inFile loaded.Files)
        let typed, typeErrors = Typecheck.check file loaded.Program
        let refused = if typeErrors.IsEmpty then ContractStyle.beforeProofs file typed else []
        if not typeErrors.IsEmpty then Rejected(inFiles typeErrors)
        elif not refused.IsEmpty then Rejected(inFiles refused)
        else
            match Smt.findZ3 s.Z3 with
            | None -> Failure("z3 not found; put it next to quod, set QUOD_Z3, or pass --z3 PATH", 2)
            | Some z3Path ->
                // flushed at each line: a log is read after a hang or a kill
                use logWriter = (match s.SmtLog with Some p -> new StreamWriter(p, AutoFlush = true) | None -> null)
                let log = if isNull logWriter then None else Some(logWriter :> TextWriter)
                use session = new Smt.Session(z3Path, s.Timeout * 1000, log, s.Cancel)
                let verified = Vcgen.verifyWith file typed session s.Budget s.RequireContracts s.Progress
                let found = verified.Diagnostics @ ContractStyle.diagnostics file typed
                let found = if s.RequireContracts then ContractStyle.required file typed found else found
                // a generic nothing uses was neither type-checked nor proved: "verified" says nothing of it
                let unused =
                    loaded.Program.Fns
                    |> List.filter (fun f -> not f.TypeParams.IsEmpty && not (typed.Fns |> List.exists (fun g -> g.Name.StartsWith(f.Name + "__"))))
                    // the standard library offers more than a program uses
                    |> List.filter (fun f ->
                        match Modules.split f.Name with
                        | Some m, _ -> not (loaded.Files.[m].StartsWith "stdlib/")
                        | None, _ -> true)
                    |> List.map (fun f ->
                        { File = file; Span = f.Span; Kind = "contract"; Status = "unused-generic"; Severity = Warning; Fn = Some f.Name
                          Property = None; Counterexample = []; Reason = None; Evidence = None
                          Message = "'" + f.Name + "' is generic and not used: it was neither type-checked nor proved. A generic is checked for the types it is used with" })
                Checked(typed, { verified with Diagnostics = loaded.Warnings @ inFiles unused @ inFiles (found @ ContractStyle.review file typed) })
    with
    | QuodError d -> Rejected(Parser.syntaxDiagnostics file src d)
    | Smt.SmtFailure message -> Failure("internal error while talking to z3: " + message, 3)
    | :? IOException as e -> Failure("internal error while talking to z3: " + e.Message, 3)
    | :? ObjectDisposedException as e -> Failure("internal error while talking to z3: " + e.Message, 3)

let errorsOf (r: Vcgen.VerifyResult) = r.Diagnostics |> List.filter (fun d -> d.Severity = Error)

let rec summary (r: Vcgen.VerifyResult) =
    let errors = errorsOf r
    let proofErrors = errors |> List.filter (fun d -> d.Kind = "proof" && d.Status <> "not-attempted") |> List.length
    let underspecified = errors |> List.filter (fun d -> d.Kind = "completeness" && d.Status <> "loose-accepts-all") |> List.length
    let looseAll = errors |> List.filter (fun d -> d.Status = "loose-accepts-all") |> List.length
    string r.Proved + " proof obligation(s) proved"
    + (if proofErrors > 0 then ", " + string proofErrors + " failed" else "")
    + (if r.NotAttempted > 0 then ", " + string r.NotAttempted + " not attempted (time budget used up)" else "")
    + "; " + string r.Determined + " of " + string r.WithContract + " contract(s) determine their result"
    + (if underspecified > 0 then ", " + string underspecified + " underspecified" else "")
    + (if looseAll > 0 then ", " + string looseAll + " with a 'loose' that accepts every result" else "")
    + styleSummary r
    + (if r.Lemmas > 0 then "; " + string r.Lemmas + " lemma(s)" else "")
    + reviewSummary r

/// "; loose: binary_search; to review with the contracts: sum (prefix_sums, range_sum)": what
/// the proofs cannot vouch for, a reviewer reads.
and private reviewSummary (r: Vcgen.VerifyResult) =
    // what each loose accepts: "binary_search (xs = [0, 0]: 0 or 1)"
    let freedom (fn: string) =
        match r.Diagnostics |> List.tryFind (fun d -> d.Kind = "loose" && d.Status = "witness" && d.Fn = Some fn) with
        | None -> fn
        | Some w ->
            let value key = w.Counterexample |> List.find (fun (k, _) -> k = key) |> snd
            let inputs = w.Counterexample |> List.filter (fun (k, _) -> k <> "result_a" && k <> "result_b")
            fn + " (" + String.Join(", ", inputs |> List.map (fun (k, x) -> k + " = " + x)) + (if inputs.IsEmpty then "" else ": ")
            + value "result_a" + " or " + value "result_b" + ")"
    let loose = r.Diagnostics |> List.filter (fun d -> d.Kind = "loose" && d.Status = "declared") |> List.choose (fun d -> d.Fn) |> List.map freedom
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
          count "none", " missing (no ensures)"; count "lemma-as-function", " lemma written as a function"
          count "pinned-input", " input fixed by its requires"
          count "returns-argument", " already guaranteed by its requires" ]
        |> List.filter (fun (n, _) -> n > 0)
        |> List.map (fun (n, text) -> string n + text)
    if parts.IsEmpty then "" else "; contracts: " + String.Join(", ", parts)

type Target =
    /// With all the requires checked at the public boundary (--check-requires all)?
    | Python of allRequires: bool
    | CSharp of CodegenCSharp.Options

/// The target named on the command line or in a tool call.
let targetOf (name: string) (ns: string option) (allRequires: bool) : Result<Target, string> =
    match name with
    | "python" -> Ok(Python allRequires)
    | "csharp" ->
        Ok(CSharp { Namespace = defaultArg ns CodegenCSharp.defaultOptions.Namespace; CheckAllRequires = allRequires })
    | t -> Result.Error("unknown target '" + t + "' (python or csharp)")

/// The code of a file and of the modules it imports (by name), and the functions not fully proved.
type Generated =
    { Code: string
      Imported: (string * string) list
      Unproved: Set<string> }

/// The file a module is written to, next to the one of the root.
let outputOf (target: Target) (file: string) =
    match target with
    | Python _ -> Path.GetFileNameWithoutExtension file + ".py"
    | CSharp _ -> CodegenCSharp.outputFile file

/// What `build` does with a checked program: the generated code, with the functions whose
/// contracts are checked at run time (--runtime-checks), or why it is not built.
let generate (target: Target) (file: string) (typed: Typed.TProgram) (r: Vcgen.VerifyResult) (runtimeChecks: bool) : Result<Generated, string> =
    let errors = errorsOf r
    let unproved = errors |> List.filter (fun d -> d.Kind = "proof") |> List.choose (fun d -> d.Fn) |> Set.ofList |> ContractStyle.dependents typed
    if errors |> List.exists (fun d -> d.Kind = "contract") then
        Result.Error "not built: --require-contracts refuses a contract, as said above"
    elif errors |> List.exists (fun d -> d.Kind = "completeness") then
        Result.Error "not built: an underspecified contract cannot be compiled (fix it, or declare the freedom with 'loose')"
    elif not unproved.IsEmpty && not runtimeChecks then
        Result.Error("not built: " + summary r + ". Fix the proofs, or build with --runtime-checks")
    else
        let shortNames (m: string option) =
            unproved |> Set.filter (fun f -> fst (Modules.split f) = m) |> Set.map (fun f -> snd (Modules.split f))
        let one (m: string option) (source: string) =
            let view = Codegen.moduleView m typed
            match target with
            | Python allRequires -> Ok(CodegenPython.generateWith source view (shortNames m) allRequires)
            | CSharp options -> CodegenCSharp.generateIn source view typed (shortNames m) options
        // a copy of a generic of another module may hold a type of this file (review of 0.3)
        (match target with
         | CSharp _ -> CodegenCSharp.setRootClass file (Codegen.moduleView None typed)
         | _ -> ())
        use _reset = { new IDisposable with member _.Dispose() = CodegenCSharp.clearRootClass () }
        one None file
        |> Result.bind (fun code ->
            let imported =
                Codegen.importedModules typed
                |> List.map (fun m -> m, one (Some m) (m + ".quod"))
            match imported |> List.tryPick (fun (_, r) -> match r with Result.Error why -> Some why | Ok _ -> None) with
            | Some why -> Result.Error why
            | None ->
                let others = imported |> List.map (fun (m, r) -> m, (match r with Ok c -> c | Result.Error _ -> ""))
                Ok { Code = code; Imported = others; Unproved = unproved })
