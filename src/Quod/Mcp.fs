/// `quod mcp`: a Model Context Protocol server on stdin/stdout, so that an AI agent uses Quod as
/// a tool, without a shell: check a program, build it, run one of its functions, read the
/// language reference. JSON-RPC 2.0, one message per line; written by hand on System.Text.Json
/// (no reflection, so it works under Native AOT, and no package to download).
module Quod.Mcp

open System
open System.IO
open System.Numerics
open System.Text
open System.Text.Json
open Quod.Diagnostics
open Quod.Typed

let private protocolVersions = [ "2025-06-18"; "2025-03-26"; "2024-11-05" ]

/// The time budget of a check through the server, unless `quod mcp --budget` says otherwise:
/// an agent waits for a tool call, and some clients cut long ones; it can ask for more with the
/// `budget` argument (first-user feedback on 0.1.0).
let defaultBudget = 60

/// The language reference: the spec from "The language" to the Python backend, embedded in the
/// binary. Not the example that follows: it is a whole solution of a VerifBench task, which agents
/// copied (run t6-haiku, binary_search through MCP).
let reference =
    lazy
        (use stream = Reflection.Assembly.GetExecutingAssembly().GetManifestResourceStream("quod-0.1.md")
         use reader = new StreamReader(stream, Encoding.UTF8)
         let spec = reader.ReadToEnd().Replace("\r\n", "\n")
         let body = spec.Substring(spec.IndexOf "## The language", spec.IndexOf "## Python backend" - spec.IndexOf "## The language")
         // without the vocabulary of the design documents, which an agent does not read
         let body =
             body.Replace(" (pillar 5)", "").Replace(" (the ⚠️ status of [principle 2](kernel.md))", "")
                 .Replace("](kernel.md)", "](https://github.com/quod-lang/quod/blob/main/spec/kernel.md)")
         "# Quod " + quodVersion + " reference\n\n" + body.TrimEnd() + "\n")

/// One section of the reference: the first heading (## or ###) that contains `title`, up to the
/// next heading of the same level or above.
let private section (title: string) : string option =
    let lines = reference.Value.Split('\n')
    let level (l: string) = if l.StartsWith "### " then 3 elif l.StartsWith "## " then 2 else 0
    match lines |> Array.tryFindIndex (fun l -> level l > 0 && l.Contains(title, StringComparison.OrdinalIgnoreCase)) with
    | None -> None
    | Some start ->
        let lv = level lines.[start]
        let stop =
            lines |> Array.indexed |> Array.tryFind (fun (i, l) -> i > start && level l > 0 && level l <= lv)
            |> Option.map fst |> Option.defaultValue lines.Length
        Some(String.Join("\n", lines.[start .. stop - 1]).TrimEnd() + "\n")

let private headings () =
    reference.Value.Split('\n') |> Array.filter (fun l -> l.StartsWith "## " || l.StartsWith "### ") |> List.ofArray

/// The reference, or one section of it (`quod reference`, and the tool quod_reference). Error:
/// no such section, with the list of sections.
let referenceText (title: string option) : Result<string, string> =
    match title with
    | None | Some "" -> Ok reference.Value
    | Some t ->
        match section t with
        | Some s -> Ok s
        | None -> Result.Error("no section '" + t + "'; the sections are:\n" + String.concat "\n" (headings ()))

// --- JSON ------------------------------------------------------------------------------

let private json (write: Utf8JsonWriter -> unit) : string =
    use ms = new MemoryStream()
    (use w = new Utf8JsonWriter(ms, JsonWriterOptions(Encoder = Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping))
     write w)
    Encoding.UTF8.GetString(ms.ToArray())

let rec private writeValue (w: Utf8JsonWriter) (v: Eval.Value) =
    match v with
    | Eval.VInt n -> if n >= BigInteger Int64.MinValue && n <= BigInteger Int64.MaxValue then w.WriteNumberValue(int64 n) else w.WriteStringValue(n.ToString())
    | Eval.VBool b -> w.WriteBooleanValue b
    | Eval.VChar c -> w.WriteStringValue(Char.ConvertFromUtf32 c)
    | Eval.VData(name, xs) ->
        w.WriteStartArray()
        w.WriteStringValue name
        for x in xs do writeValue w x
        w.WriteEndArray()
    | Eval.VSeq xs when not xs.IsEmpty && xs |> List.forall (function Eval.VChar _ -> true | _ -> false) ->
        w.WriteStringValue(String.Join("", xs |> List.map (function Eval.VChar c -> Char.ConvertFromUtf32 c | _ -> "")))
    | Eval.VSeq xs | Eval.VTuple xs ->
        w.WriteStartArray()
        for x in xs do writeValue w x
        w.WriteEndArray()

/// A JSON argument as a value of type t: integers as numbers (or strings, for big ones), booleans,
/// sequences and tuples as arrays.
let rec private readValue (t: Ty) (e: JsonElement) : Eval.Value option =
    match t, e.ValueKind with
    | (TyInt | TyNat | TyI32 | TyI64), JsonValueKind.Number ->
        match BigInteger.TryParse(e.GetRawText()) with
        | true, n -> Some(Eval.VInt n)
        | _ -> None
    | (TyInt | TyNat | TyI32 | TyI64), JsonValueKind.String ->
        match BigInteger.TryParse(e.GetString()) with
        | true, n -> Some(Eval.VInt n)
        | _ -> None
    | TyChar, JsonValueKind.String ->
        match [ for r in e.GetString().EnumerateRunes() -> r.Value ] with
        | [ c ] -> Some(Eval.VChar c)
        | _ -> None
    | TySeq TyChar, JsonValueKind.String ->
        Some(Eval.VSeq [ for r in e.GetString().EnumerateRunes() -> Eval.VChar r.Value ])
    | TyBool, JsonValueKind.True -> Some(Eval.VBool true)
    | TyBool, JsonValueKind.False -> Some(Eval.VBool false)
    | TySeq el, JsonValueKind.Array ->
        let items = [ for x in e.EnumerateArray() -> readValue el x ]
        if List.forall Option.isSome items then Some(Eval.VSeq(List.map Option.get items)) else None
    | TyTuple ts, JsonValueKind.Array when e.GetArrayLength() = ts.Length ->
        let items = List.map2 readValue ts [ for x in e.EnumerateArray() -> x ]
        if List.forall Option.isSome items then Some(Eval.VTuple(List.map Option.get items)) else None
    | _ -> None

// --- tools -----------------------------------------------------------------------------

/// The result of a tool: a text for the agent, the same facts as JSON, and whether it is an
/// error (a tool that could not do its job, not a program that does not verify).
type private ToolResult = { Text: string; Structured: string; IsError: bool }

exception private ToolError of string

let private failTool message = raise (ToolError message)

let private str (args: JsonElement) (name: string) =
    match args.TryGetProperty name with
    | true, v when v.ValueKind = JsonValueKind.String -> Some(v.GetString())
    | _ -> None

let private int' (args: JsonElement) (name: string) =
    match args.TryGetProperty name with
    | true, v when v.ValueKind = JsonValueKind.Number -> Some(v.GetInt32())
    | _ -> None

let private bool' (args: JsonElement) (name: string) =
    match args.TryGetProperty name with
    | true, v when v.ValueKind = JsonValueKind.True -> true
    | _ -> false

/// The program of a tool call: `source` (the text) or `path` (a file, relative to the server's
/// working directory). The name is what diagnostics show.
let private program (args: JsonElement) : string * string =
    match str args "source", str args "path" with
    | Some src, _ -> defaultArg (str args "file_name") "input.quod", src
    | None, Some p when File.Exists p -> p, File.ReadAllText p
    | None, Some p -> failTool ("file not found: " + p + " (relative to " + Directory.GetCurrentDirectory() + ")")
    | None, None -> failTool "give the program as 'source' (its text) or 'path' (a file)"

let private settings (base': Pipeline.Settings) (args: JsonElement) =
    { base' with Timeout = defaultArg (int' args "timeout") base'.Timeout; Budget = defaultArg (int' args "budget") base'.Budget }

/// Evaluate a function's contract, not its code: for each case `{"args": [...], "results": [...]}`,
/// whether its requires accept the arguments, and whether its ensures accept each result, as true,
/// false, or null when the evaluator cannot tell. The bench measures contracts with it (bench/heldout.md).
let contractCases (file: string) (src: string) (fn: string) (casesJson: string) : Result<string, string> =
    let prog =
        match Modules.load file src with
        | Ok loaded -> loaded.Program
        | Result.Error(d :: _) -> raise (QuodError d)
        | Result.Error [] -> failwith "unreachable: an error without a diagnostic"
    let typed, errors = Typecheck.check file prog
    if not errors.IsEmpty then Result.Error "the program has type errors"
    else
        match typed.Fns |> List.tryFind (fun f -> f.Name = fn) with
        | None -> Result.Error("no function '" + fn + "'")
        | Some f ->
            let ev = Eval.Evaluator(typed.Fns |> List.map (fun g -> g.Name, g) |> Map.ofList)
            let verdict (clauses: TExpr list) (env: Map<string, Eval.Value>) =
                let holds = clauses |> List.map (fun e -> ev.Holds(e, env))
                if holds |> List.contains (Some false) then Some false
                elif holds |> List.contains None then None
                else Some true
            let write (w: Utf8JsonWriter) (v: bool option) =
                match v with
                | Some b -> w.WriteBooleanValue b
                | None -> w.WriteNullValue()
            use doc = JsonDocument.Parse casesJson
            Ok(
                Eval.withBigStack (fun () ->
                    json (fun w ->
                        w.WriteStartArray()
                        for case in doc.RootElement.EnumerateArray() do
                            let args = List.map2 (fun (p: TParam) a -> p.Name, readValue p.Ty a) f.Params [ for a in case.GetProperty("args").EnumerateArray() -> a ]
                            w.WriteStartObject()
                            if args |> List.exists (fun (_, a) -> a.IsNone) then
                                w.WriteString("error", "an argument does not fit its type")
                            else
                                let env = args |> List.map (fun (n, a) -> n, a.Value) |> Map.ofList
                                let fits = List.forall2 (fun (p: TParam) (_, a: Eval.Value option) -> ev.Fits(p.Ty, a.Value)) f.Params args
                                w.WritePropertyName "requires"
                                write w (if fits then verdict f.Requires env else Some false)
                                w.WriteStartArray "results"
                                for r in case.GetProperty("results").EnumerateArray() do
                                    match readValue f.Ret r with
                                    | Some value when ev.Fits(f.Ret, value) -> write w (verdict f.Ensures (env.Add("result", value)))
                                    | _ -> w.WriteBooleanValue false
                                w.WriteEndArray()
                            w.WriteEndObject()
                        w.WriteEndArray())))

/// The diagnostics as the command line prints them (notes are in the summary).
let private reportText (ds: Diagnostic list) =
    ds |> List.filter (fun d -> d.Severity <> Info) |> List.map toText |> String.concat "\n"

let private writeDiagnostics (w: Utf8JsonWriter) (ds: Diagnostic list) =
    w.WriteStartArray("diagnostics")
    for d in ds do writeDiagnostic w d
    w.WriteEndArray()

let private check (base': Pipeline.Settings) (args: JsonElement) : ToolResult =
    let file, src = program args
    match Pipeline.check file src (settings base' args) with
    | Pipeline.Failure(message, _) -> failTool message
    | Pipeline.Rejected ds ->
        let line = "rejected: " + string ds.Length + " syntax or type error(s); nothing was proved"
        { Text = reportText ds + "\n" + line
          Structured = json (fun w -> w.WriteStartObject(); w.WriteBoolean("verified", false); w.WriteString("summary", line); writeDiagnostics w ds; w.WriteEndObject())
          IsError = false }
    | Pipeline.Checked(_, r) ->
        let ok = (Pipeline.errorsOf r).IsEmpty
        let line = (if ok then "verified: " else "rejected: ") + Pipeline.summary r
        let report = reportText r.Diagnostics
        { Text = (if report = "" then line else report + "\n" + line)
          Structured = json (fun w -> w.WriteStartObject(); w.WriteBoolean("verified", ok); w.WriteString("summary", line); writeDiagnostics w r.Diagnostics; w.WriteEndObject())
          IsError = false }

let private build (base': Pipeline.Settings) (args: JsonElement) : ToolResult =
    let target =
        match Pipeline.targetOf (defaultArg (str args "target") "python") (str args "namespace") (str args "check_requires" = Some "all") with
        | Ok t -> t
        | Result.Error why -> failTool why
    let file, src = program args
    let notBuilt (why: string) (ds: Diagnostic list) =
        { Text = (match reportText ds with "" -> why | r -> r + "\n" + why)
          Structured = json (fun w -> w.WriteStartObject(); w.WriteBoolean("built", false); w.WriteString("summary", why); writeDiagnostics w ds; w.WriteEndObject())
          IsError = false }
    match Pipeline.check file src (settings base' args) with
    | Pipeline.Failure(message, _) -> failTool message
    | Pipeline.Rejected ds -> notBuilt ("not built: " + string ds.Length + " syntax or type error(s)") ds
    | Pipeline.Checked(typed, r) ->
        match Pipeline.generate target file typed r (bool' args "runtime_checks") with
        | Result.Error why -> notBuilt why r.Diagnostics
        | Ok generated ->
            let code, unproved = generated.Code, generated.Unproved
            let line =
                "built (" + Pipeline.summary r + ")"
                + (if unproved.IsEmpty then "" else "; not fully proved, contracts checked at run time in: " + String.Join(", ", unproved))
            let others = generated.Imported |> List.map (fun (m, text) -> "--- module " + m + " ---\n\n" + text)
            { Text = String.Join("\n\n", line :: code :: others)
              Structured =
                json (fun w ->
                    w.WriteStartObject()
                    w.WriteBoolean("built", true)
                    w.WriteString("summary", line)
                    w.WriteString("language", (match target with Pipeline.Python _ -> "python" | Pipeline.CSharp _ -> "csharp"))
                    w.WriteString("code", code)
                    w.WriteStartObject "imported"
                    for m, text in generated.Imported do w.WriteString(m, text)
                    w.WriteEndObject()
                    w.WriteStartArray("runtime_checked")
                    for f in unproved do w.WriteStringValue f
                    w.WriteEndArray()
                    writeDiagnostics w r.Diagnostics
                    w.WriteEndObject())
              IsError = false }

/// "an int", "a nat", "a seq<int>": a type in a sentence.
let private aType (t: Ty) =
    let text = tyText t
    (if text.StartsWith "i" then "an " else "a ") + text

/// Run one function on given arguments with the evaluator, checking every obligation on the way
/// (as `quod check` does before asking the solver): its result, or the obligation it breaks.
let private run (args: JsonElement) : ToolResult =
    let file, src = program args
    let name = match str args "function" with Some n -> n | None -> failTool "give the 'function' to run"
    let typed =
        try
            match Modules.load file src with
            | Result.Error ds -> failTool ("the program does not parse or import:\n" + reportText ds)
            | Ok loaded ->
            match Typecheck.check file loaded.Program with
            | t, [] -> t
            | _, errs -> failTool ("the program does not type-check:\n" + reportText (errs |> List.map (Modules.inFile loaded.Files)))
        with QuodError d -> failTool ("the program does not parse:\n" + reportText (Parser.syntaxDiagnostics file src d))
    let f =
        match typed.Fns |> List.tryFind (fun f -> f.Name = name) with
        | Some f -> f
        | None -> failTool ("no function '" + name + "' (there are: " + String.Join(", ", typed.Fns |> List.map (fun f -> f.Name)) + ")")
    let given =
        match args.TryGetProperty "args" with
        | true, a when a.ValueKind = JsonValueKind.Array -> [ for x in a.EnumerateArray() -> x ]
        | _ -> []
    if given.Length <> f.Params.Length then
        failTool ("'" + name + "' takes " + string f.Params.Length + " argument(s): " + String.Join(", ", f.Params |> List.map (fun p -> p.Name + ": " + tyText p.Ty)))
    let values =
        List.map2 (fun (p: TParam) x ->
            match readValue p.Ty x with
            | Some v -> v
            | None -> failTool ("argument '" + p.Name + "' is not " + aType p.Ty + ": " + x.GetRawText())) f.Params given
    let fns = typed.Fns |> List.map (fun f -> f.Name, f) |> Map.ofList
    let plain = Eval.Evaluator(fns)
    let env = List.zip (f.Params |> List.map (fun p -> p.Name)) values |> Map.ofList
    let notFit = List.zip f.Params values |> List.tryFind (fun (p, v) -> not (plain.Fits(p.Ty, v)))
    let failedRequires =
        List.indexed f.Requires |> List.tryFind (fun (_, r) -> plain.Holds(r, env) <> Some true)
    let outcome (status: string) (text: string) (extra: Utf8JsonWriter -> unit) =
        { Text = text
          Structured = json (fun w -> w.WriteStartObject(); w.WriteString("status", status); extra w; w.WriteEndObject())
          IsError = false }
    match notFit, failedRequires with
    | Some(p, v), _ -> outcome "invalid-input" ("argument '" + p.Name + "' = " + Eval.valueText v + " is not " + aType p.Ty) ignore
    | _, Some(k, r) ->
        outcome "requires-false" ("the requires #" + string (k + 1) + " does not hold for these arguments: " + Printer.exprText (toSyntax r))
            (fun w -> w.WriteNumber("requires", k + 1))
    | None, None ->
        let ev = Eval.Evaluator(fns, true)
        try
            let v = Eval.withBigStack (fun () -> ev.Run(f, values))
            outcome "ok" (name + " returns " + (match f.Ret, v with TySeq TyChar, Eval.VSeq [] -> "\"\"" | _ -> Eval.valueText v)) (fun w -> w.WritePropertyName "result"; (match f.Ret, v with TySeq TyChar, Eval.VSeq [] -> w.WriteStringValue "" | _ -> writeValue w v))
        with
        | Eval.Violation(label, span) ->
            // what was broken: the clause of a postcondition, else the source line; and for a
            // postcondition, the value returned (test of 0.1.1: the agent had to reread the source)
            let ensuresNumber =
                if label.StartsWith "postcondition (ensures #" then
                    match Int32.TryParse(label.Substring(24).TrimEnd(')')) with
                    | true, k when k >= 1 && k <= f.Ensures.Length -> Some k
                    | _ -> None
                else None
            let returned = if ensuresNumber.IsSome then ev.CheckedResult else None
            let what =
                match ensuresNumber with
                | Some k -> Printer.exprText (toSyntax f.Ensures.[k - 1])
                | None ->
                    let lines = src.Replace("\r\n", "\n").Split('\n')
                    if span.Start.Line >= 1 && span.Start.Line <= lines.Length then lines.[span.Start.Line - 1].Trim() else ""
            let call = name + "(" + String.Join(", ", values |> List.map Eval.valueText) + ")"
            let text =
                file + "(" + string span.Start.Line + "," + string span.Start.Col + "): " + call
                + (match returned with Some v -> " returned " + Eval.valueText v + ", but " | None -> ": ")
                + label + " fails: `" + what + "`"
            outcome "violation" text (fun w ->
                w.WriteString("property", label)
                w.WriteString("text", what)
                returned |> Option.iter (fun v -> w.WritePropertyName "returned"; writeValue w v)
                w.WriteNumber("line", span.Start.Line)
                w.WriteNumber("col", span.Start.Col))
        | Eval.CannotEvaluate why -> outcome "not-evaluated" ("could not run '" + name + "': " + why) (fun w -> w.WriteString("reason", why))

let private referenceTool (args: JsonElement) : ToolResult =
    let text =
        match referenceText (str args "section") with
        | Ok text -> text
        | Result.Error message -> failTool message
    { Text = text; Structured = json (fun w -> w.WriteStartObject(); w.WriteString("reference", text); w.WriteEndObject()); IsError = false }

// --- the server ------------------------------------------------------------------------

let private programProperties =
    "\"source\": {\"type\": \"string\", \"description\": \"The Quod program, as text\"},"
    + "\"path\": {\"type\": \"string\", \"description\": \"Or a .quod file, relative to the server's working directory\"},"
    + "\"file_name\": {\"type\": \"string\", \"description\": \"The name shown in diagnostics when 'source' is given\"}"

let private budgetProperties =
    "\"timeout\": {\"type\": \"integer\", \"description\": \"Seconds per proof obligation (default 10)\"},"
    + "\"budget\": {\"type\": \"integer\", \"description\": \"Seconds for the whole check (default 60, 0 for none): obligations left when it is used up are reported as not attempted\"}"

/// name, description, input schema
let private tools =
    [ "quod_check",
      "Check a Quod program: types, proofs of every contract with the z3 solver, and completeness (each contract must determine its result). "
      + "Before the solver, each function runs on small inputs: a broken obligation comes with a confirmed counterexample. "
      + "Returns the diagnostics and a summary line that starts with 'verified' or 'rejected'. Fix the program until it is verified.",
      "{\"type\": \"object\", \"properties\": {" + programProperties + "," + budgetProperties + "}}"
      "quod_build",
      "Check a Quod program, then generate its Python module or C# class (returned as text, no file is written). Only a verified program is built, "
      + "unless runtime_checks is true: the contracts that are not proved are then checked at run time (an underspecified contract still blocks the build).",
      "{\"type\": \"object\", \"properties\": {" + programProperties + "," + budgetProperties
      + ",\"target\": {\"type\": \"string\", \"enum\": [\"python\", \"csharp\"]}, \"runtime_checks\": {\"type\": \"boolean\"}, "
      + "\"namespace\": {\"type\": \"string\", \"description\": \"C#: the namespace of the class\"}, "
      + "\"check_requires\": {\"type\": \"string\", \"enum\": [\"all\"], \"description\": \"Also check the quantified requires when a public function is called\"}}}"
      "quod_run",
      "Run one function of a Quod program on given arguments, checking every assertion, invariant, bound and contract on the way, without the solver. "
      + "Integers are JSON numbers (or strings for big ones), sequences and tuples are arrays. Returns the result, or the obligation that fails, with its text (and the value returned, for a postcondition).",
      "{\"type\": \"object\", \"properties\": {" + programProperties
      + ",\"function\": {\"type\": \"string\"}, \"args\": {\"type\": \"array\", \"description\": \"One JSON value per parameter, in order\"}}, \"required\": [\"function\"]}"
      "quod_reference",
      "The Quod language reference: syntax, types, contracts, lemmas, verification, completeness, diagnostics, command line. "
      + "Read it before writing Quod. Give a section title (e.g. 'Hints and lemmas', 'Contract style') to get only that section.",
      "{\"type\": \"object\", \"properties\": {\"section\": {\"type\": \"string\"}}}" ]

let private instructions =
    "Quod is a language in which every function carries a contract that the compiler proves, and every contract must determine its result. "
    + "To write a function in Quod: read quod_reference once, write the program, call quod_check until it says 'verified' "
    + "(a counterexample shows the inputs that break the code or the contract), then quod_build to get the Python module."

/// Handle one JSON-RPC message; the response to write, if any (notifications get none).
let handle (settings: Pipeline.Settings) (line: string) : string option =
    let response (id: JsonElement option) (body: Utf8JsonWriter -> unit) =
        Some(
            json (fun w ->
                w.WriteStartObject()
                w.WriteString("jsonrpc", "2.0")
                match id with
                | Some i -> w.WritePropertyName "id"; i.WriteTo w
                | None -> w.WriteNull "id"
                body w
                w.WriteEndObject()))
    let error id (code: int) (message: string) =
        response id (fun w -> w.WriteStartObject "error"; w.WriteNumber("code", code); w.WriteString("message", message); w.WriteEndObject())
    let result id (write: Utf8JsonWriter -> unit) = response id (fun w -> w.WriteStartObject "result"; write w; w.WriteEndObject())
    let doc = try Some(JsonDocument.Parse line) with :? JsonException -> None
    match doc with
    | None -> error None -32700 "parse error"
    | Some doc ->
        use doc = doc
        let root = doc.RootElement
        let id = match root.TryGetProperty "id" with | true, i -> Some(i.Clone()) | _ -> None
        let method' = match root.TryGetProperty "method" with | true, m when m.ValueKind = JsonValueKind.String -> m.GetString() | _ -> ""
        let params' = match root.TryGetProperty "params" with | true, p -> Some p | _ -> None
        match method', id with
        | _, None -> None // a notification (initialized, cancelled...): nothing to answer
        | "initialize", _ ->
            let asked =
                params' |> Option.bind (fun p -> match p.TryGetProperty "protocolVersion" with | true, v -> Some(v.GetString()) | _ -> None)
            let version = match asked with Some v when List.contains v protocolVersions -> v | _ -> protocolVersions.Head
            result id (fun w ->
                w.WriteString("protocolVersion", version)
                w.WriteStartObject "capabilities"
                w.WriteStartObject "tools"; w.WriteEndObject()
                w.WriteStartObject "resources"; w.WriteEndObject()
                w.WriteEndObject()
                w.WriteStartObject "serverInfo"; w.WriteString("name", "quod"); w.WriteString("version", quodVersion); w.WriteEndObject()
                w.WriteString("instructions", instructions))
        | "ping", _ -> result id ignore
        | "tools/list", _ ->
            result id (fun w ->
                w.WriteStartArray "tools"
                for (name, description, schema) in tools do
                    w.WriteStartObject()
                    w.WriteString("name", name)
                    w.WriteString("description", description)
                    w.WritePropertyName "inputSchema"
                    w.WriteRawValue schema
                    w.WriteEndObject()
                w.WriteEndArray())
        | "tools/call", _ ->
            let name = params' |> Option.bind (fun p -> match p.TryGetProperty "name" with | true, n -> Some(n.GetString()) | _ -> None)
            let args =
                match params' |> Option.map (fun p -> p.TryGetProperty "arguments") with
                | Some(true, a) when a.ValueKind = JsonValueKind.Object -> a
                | _ -> JsonDocument.Parse("{}").RootElement
            let outcome =
                try
                    match name with
                    | Some "quod_check" -> Ok(check settings args)
                    | Some "quod_build" -> Ok(build settings args)
                    | Some "quod_run" -> Ok(run args)
                    | Some "quod_reference" -> Ok(referenceTool args)
                    | other -> Result.Error(-32602, "unknown tool: " + defaultArg other "(none)")
                with ToolError message ->
                    Ok { Text = message; Structured = json (fun w -> w.WriteStartObject(); w.WriteString("error", message); w.WriteEndObject()); IsError = true }
            match outcome with
            | Result.Error(code, message) -> error id code message
            | Ok r ->
                result id (fun w ->
                    w.WriteStartArray "content"
                    w.WriteStartObject(); w.WriteString("type", "text"); w.WriteString("text", r.Text); w.WriteEndObject()
                    w.WriteEndArray()
                    w.WritePropertyName "structuredContent"
                    w.WriteRawValue r.Structured
                    w.WriteBoolean("isError", r.IsError))
        | "resources/list", _ ->
            result id (fun w ->
                w.WriteStartArray "resources"
                w.WriteStartObject()
                w.WriteString("uri", "quod://reference")
                w.WriteString("name", "Quod language reference")
                w.WriteString("mimeType", "text/markdown")
                w.WriteEndObject()
                w.WriteEndArray())
        | "resources/read", _ ->
            let uri = params' |> Option.bind (fun p -> match p.TryGetProperty "uri" with | true, u -> Some(u.GetString()) | _ -> None)
            if uri = Some "quod://reference" then
                result id (fun w ->
                    w.WriteStartArray "contents"
                    w.WriteStartObject()
                    w.WriteString("uri", "quod://reference")
                    w.WriteString("mimeType", "text/markdown")
                    w.WriteString("text", reference.Value)
                    w.WriteEndObject()
                    w.WriteEndArray())
            else error id -32002 ("resource not found: " + defaultArg uri "(none)")
        | m, _ -> error id -32601 ("method not found: " + m)

/// Serve on stdin/stdout until stdin closes. Logs go to stderr only: stdout is the protocol.
/// Tool calls run one at a time on a worker thread, so that the reader stays responsive (test of
/// 0.1.1): ping, tools/list and the resources are answered at once, even during a long check,
/// and notifications/cancelled stops the call it names (z3 is killed, and no response is sent,
/// as MCP asks). A call that gives a progressToken gets a progress notification after each
/// function checked.
let serve (settings: Pipeline.Settings) : int =
    use input = new StreamReader(Console.OpenStandardInput(), UTF8Encoding(false))
    use output = new StreamWriter(Console.OpenStandardOutput(), UTF8Encoding(false))
    output.AutoFlush <- true
    let gate = obj ()
    let write (message: string) = lock gate (fun () -> output.Write(message + "\n"))
    /// Tool calls not answered yet, by the JSON text of their id: to cancel them.
    let pending = Collections.Concurrent.ConcurrentDictionary<string, Threading.CancellationTokenSource>()
    let calls = new Collections.Concurrent.BlockingCollection<string * string * JsonElement option>()
    let worker =
        Threading.Thread(
            (fun () ->
                for (line, id, token) in calls.GetConsumingEnumerable() do
                    match pending.TryGetValue id with
                    | true, cts when not cts.IsCancellationRequested ->
                        let progress (d: float) (t: int) (what: string) =
                            token |> Option.iter (fun tok ->
                                write (
                                    json (fun w ->
                                        w.WriteStartObject()
                                        w.WriteString("jsonrpc", "2.0")
                                        w.WriteString("method", "notifications/progress")
                                        w.WriteStartObject "params"
                                        w.WritePropertyName "progressToken"
                                        tok.WriteTo w
                                        w.WriteNumber("progress", d)
                                        w.WriteNumber("total", t)
                                        w.WriteString("message", what)
                                        w.WriteEndObject()
                                        w.WriteEndObject())))
                        let response =
                            try handle { settings with Cancel = cts.Token; Progress = progress } line
                            with e ->
                                Console.Error.WriteLine("quod mcp: " + e.Message)
                                None
                        if not cts.IsCancellationRequested then response |> Option.iter write
                        pending.TryRemove id |> ignore
                        cts.Dispose()
                    | _ -> pending.TryRemove id |> ignore),
            256 * 1024 * 1024)
    worker.IsBackground <- true
    worker.Start()
    let mutable line = input.ReadLine()
    while not (isNull line) do
        if line.Trim() <> "" then
            try
                let route =
                    try
                        use doc = JsonDocument.Parse line
                        let root = doc.RootElement
                        let method' = match root.TryGetProperty "method" with | true, m when m.ValueKind = JsonValueKind.String -> m.GetString() | _ -> ""
                        let id = match root.TryGetProperty "id" with | true, i -> Some(i.GetRawText()) | _ -> None
                        let params' = match root.TryGetProperty "params" with | true, p when p.ValueKind = JsonValueKind.Object -> Some p | _ -> None
                        let cancelled =
                            params' |> Option.bind (fun p -> match p.TryGetProperty "requestId" with | true, r -> Some(r.GetRawText()) | _ -> None)
                        let token =
                            params'
                            |> Option.bind (fun p -> match p.TryGetProperty "_meta" with | true, m when m.ValueKind = JsonValueKind.Object -> Some m | _ -> None)
                            |> Option.bind (fun m -> match m.TryGetProperty "progressToken" with | true, t -> Some(t.Clone()) | _ -> None)
                        Some(method', id, cancelled, token)
                    with :? JsonException -> None
                match route with
                | Some("notifications/cancelled", _, Some requestId, _) ->
                    match pending.TryGetValue requestId with
                    | true, cts -> (try cts.Cancel() with :? ObjectDisposedException -> ())
                    | _ -> ()
                | Some("tools/call", Some id, _, token) ->
                    pending.[id] <- new Threading.CancellationTokenSource()
                    calls.Add((line, id, token))
                | _ -> handle settings line |> Option.iter write
            with e -> Console.Error.WriteLine("quod mcp: " + e.Message)
        line <- input.ReadLine()
    calls.CompleteAdding()
    worker.Join()
    0
