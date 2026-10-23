/// The `quod` command line: `parse`, `check` (types, proofs, completeness), `build`.
module Quod.Program

open System
open System.IO
open Quod.Diagnostics

let private usage =
    "usage: quod <command> FILE [options]\n"
    + "  parse   read FILE, report the first syntax error, or print the program back\n"
    + "  check   type-check FILE, prove its contracts, check that they are complete\n"
    + "  build   check FILE, then generate code (only for a verified program)\n"
    + "options:\n"
    + "  --json              diagnostics as JSON\n"
    + "  --z3 PATH           the z3 executable (default: next to quod, $QUOD_Z3, then PATH)\n"
    + "  --timeout SECONDS   time limit per proof obligation (default 10)\n"
    + "  --smt-log FILE      write every command sent to z3 to FILE\n"
    + "  --target python     code generation target (build; python is the only one in 0.1)\n"
    + "  -o DIR              output directory (build; default: next to FILE)\n"
    + "  --runtime-checks    build even if some proofs fail: their contracts become run-time\n"
    + "                      assertions (an underspecified contract still blocks the build)"

type private Options =
    { Json: bool
      Z3: string option
      Timeout: int
      SmtLog: string option
      Target: string
      OutDir: string option
      RuntimeChecks: bool }

let private parseOptions (args: string list) : Options * string list =
    let rec go (o: Options) (rest: string list) (positional: string list) =
        match rest with
        | "--json" :: tl -> go { o with Json = true } tl positional
        | "--z3" :: p :: tl -> go { o with Z3 = Some p } tl positional
        | "--timeout" :: s :: tl -> go { o with Timeout = int s } tl positional
        | "--smt-log" :: p :: tl -> go { o with SmtLog = Some p } tl positional
        | "--target" :: t :: tl -> go { o with Target = t } tl positional
        | "-o" :: d :: tl -> go { o with OutDir = Some d } tl positional
        | "--runtime-checks" :: tl -> go { o with RuntimeChecks = true } tl positional
        | x :: tl -> go o tl (positional @ [ x ])
        | [] -> o, positional
    go { Json = false; Z3 = None; Timeout = 10; SmtLog = None; Target = "python"; OutDir = None; RuntimeChecks = false } args []

let private report (o: Options) (ds: Diagnostic list) =
    if o.Json then Console.WriteLine(toJson ds)
    else for d in ds do if d.Severity <> Info then Console.Error.WriteLine(toText d) // notes: in the summary

let private withFile (file: string) (action: string -> int) =
    if File.Exists file then action (File.ReadAllText file)
    else
        Console.Error.WriteLine("error: " + file + " not found")
        2

let private parseCommand (file: string) (o: Options) =
    withFile file (fun src ->
        try
            let program = Parser.parseProgram file src
            if o.Json then report o [] else Console.Write(Printer.programText program)
            0
        with QuodError d ->
            report o [ d ]
            1)

/// Parse, type-check, prove and check completeness. Ok with the typed program and the
/// verification result, or Error with the exit code once everything has been reported.
let private verifyFile (file: string) (src: string) (o: Options) : Result<Typed.TProgram * Vcgen.VerifyResult, int> =
    try
        let program = Parser.parseProgram file src
        let typed, typeErrors = Typecheck.check file program
        if not typeErrors.IsEmpty then
            report o typeErrors
            Result.Error 1
        else
            match Smt.findZ3 o.Z3 with
            | None ->
                Console.Error.WriteLine("error: z3 not found; put it next to quod, set QUOD_Z3, or pass --z3 PATH")
                Result.Error 2
            | Some z3Path ->
                use logWriter = (match o.SmtLog with Some p -> new StreamWriter(p) | None -> null)
                let log = if isNull logWriter then None else Some(logWriter :> TextWriter)
                use session = new Smt.Session(z3Path, o.Timeout * 1000, log)
                let verified = Vcgen.verify file typed session
                let result = { verified with Diagnostics = verified.Diagnostics @ ContractStyle.diagnostics file typed }
                report o result.Diagnostics
                Ok(typed, result)
    with
    | QuodError d ->
        report o [ d ]
        Result.Error 1
    | Smt.SmtFailure message ->
        Console.Error.WriteLine("internal error while talking to z3: " + message)
        Result.Error 3

let private errorsOf (r: Vcgen.VerifyResult) = r.Diagnostics |> List.filter (fun d -> d.Severity = Error)

let rec private summary (r: Vcgen.VerifyResult) =
    let errors = errorsOf r
    let proofErrors = errors |> List.filter (fun d -> d.Kind = "proof") |> List.length
    let underspecified = errors |> List.filter (fun d -> d.Kind = "completeness") |> List.length
    string r.Proved + " proof obligation(s) proved"
    + (if proofErrors > 0 then ", " + string proofErrors + " failed" else "")
    + "; " + string r.Determined + " of " + string r.WithContract + " contract(s) determine their result"
    + (if underspecified > 0 then ", " + string underspecified + " underspecified" else "")
    + styleSummary r

/// "; contracts: 2 by properties, 1 by a model, 1 restating the body" (the styles present).
and private styleSummary (r: Vcgen.VerifyResult) =
    let count status = r.Diagnostics |> List.filter (fun d -> d.Kind = "contract" && d.Status = status) |> List.length
    let parts =
        [ count "properties", " by properties"; count "model", " by a model"; count "restated", " restating the body" ]
        |> List.filter (fun (n, _) -> n > 0)
        |> List.map (fun (n, text) -> string n + text)
    if parts.IsEmpty then "" else "; contracts: " + String.Join(", ", parts)

let private checkCommand (file: string) (o: Options) =
    withFile file (fun src ->
        match verifyFile file src o with
        | Result.Error code -> code
        | Ok(_, result) ->
            let errors = errorsOf result
            if not o.Json then
                let line = (if errors.IsEmpty then "verified: " else "rejected: ") + summary result
                if errors.IsEmpty then Console.WriteLine line else Console.Error.WriteLine line
            if errors.IsEmpty then 0 else 1) // an inconclusive completeness verdict is a warning only

let private buildCommand (file: string) (o: Options) =
    if o.Target <> "python" then
        Console.Error.WriteLine("error: unknown target '" + o.Target + "' (Quod 0.1 generates python only)")
        2
    else
        withFile file (fun src ->
            match verifyFile file src o with
            | Result.Error code -> code
            | Ok(typed, result) ->
                let errors = errorsOf result
                let underspecified = errors |> List.exists (fun d -> d.Kind = "completeness")
                let unproved = errors |> List.filter (fun d -> d.Kind = "proof") |> List.choose (fun d -> d.Fn) |> Set.ofList
                if underspecified then
                    Console.Error.WriteLine("not built: an underspecified contract cannot be compiled (fix it, or declare the freedom with 'loose')")
                    1
                elif not unproved.IsEmpty && not o.RuntimeChecks then
                    Console.Error.WriteLine("not built: " + summary result + ". Fix the proofs, or build with --runtime-checks")
                    1
                else
                    let dir = defaultArg o.OutDir (Path.GetDirectoryName(Path.GetFullPath file))
                    Directory.CreateDirectory dir |> ignore
                    let target = Path.Combine(dir, Path.GetFileNameWithoutExtension file + ".py")
                    File.WriteAllText(target, CodegenPython.generate file typed unproved)
                    if not o.Json then
                        Console.WriteLine("built " + target + " (" + summary result + ")")
                        if not unproved.IsEmpty then
                            Console.Error.WriteLine(
                                "warning: not fully proved, contracts checked at run time in: " + String.Join(", ", unproved))
                    0)

[<EntryPoint>]
let main argv =
    let o, args = parseOptions (List.ofArray argv)
    match args with
    | [ "parse"; file ] -> parseCommand file o
    | [ "check"; file ] -> checkCommand file o
    | [ "build"; file ] -> buildCommand file o
    | [ "--version" ] ->
        Console.WriteLine("quod 0.1.0-dev")
        0
    | _ ->
        Console.Error.WriteLine(usage)
        2
