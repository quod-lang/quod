/// Diagnostics shared by every stage: one record, printed for humans or written as JSON.
/// JSON is written with Utf8JsonWriter by hand: no reflection, so it works under Native AOT.
module Quod.Diagnostics

open System.IO
open System.Text
open System.Text.Json
open Quod.Syntax

/// The version of quod, in --version and in the header of generated code.
let quodVersion = "0.1.4"

type Severity =
    | Error
    | Warning
    /// Information for the report (contract style): not printed with the findings in text mode.
    | Info

type Diagnostic =
    { File: string
      Span: Span
      /// syntax | type | proof | completeness | contract
      Kind: string
      /// error | refuted | underspecified | inconclusive; for contract: properties | model | restated
      Status: string
      Severity: Severity
      Fn: string option
      Property: string option
      /// Values of the parameters that make a proof obligation fail (name, Quod value).
      Counterexample: (string * string) list
      /// Why the solver gave no verdict (inconclusive): timeout, or its reason-unknown text.
      Reason: string option
      /// Where a counterexample comes from: run (the function was run on it, a certain
      /// failure), solver (a model of the negated obligation), unconfirmed (a candidate model).
      Evidence: string option
      Message: string }

/// Raised by a stage that stops at its first error (the parser does in 0.1).
exception QuodError of Diagnostic

let syntaxError (file: string) (span: Span) (message: string) =
    QuodError
        { File = file; Span = span; Kind = "syntax"; Status = "error"; Severity = Error
          Fn = None; Property = None; Counterexample = []; Reason = None; Evidence = None; Message = message }

let private severityText = function Error -> "error" | Warning -> "warning" | Info -> "note"

/// `file(line,col): error: message`, the format editors and agents already recognise.
/// The code of a diagnostic in a build: what NoWarn and WarningsAsErrors understand.
let private buildCode (d: Diagnostic) =
    match d.Kind with
    | "syntax" -> "QUOD0001"
    | "type" -> "QUOD0002"
    | "proof" -> "QUOD0003"
    | "completeness" -> "QUOD0004"
    | "contract" -> "QUOD0005"
    | "loose" -> "QUOD0006"
    | _ -> "QUOD0007"

let toText (d: Diagnostic) =
    let sb = StringBuilder()
    sb.Append(d.File).Append('(').Append(d.Span.Start.Line).Append(',').Append(d.Span.Start.Col)
      .Append("): ").Append(severityText d.Severity).Append(": ") |> ignore
    match d.Fn with
    | Some f -> sb.Append("in ").Append(f).Append(": ") |> ignore
    | None -> ()
    sb.Append(d.Message) |> ignore
    if not d.Counterexample.IsEmpty then
        sb.Append(if d.Kind = "completeness" then "\n    witness: " else "\n    counterexample: ").Append(d.Counterexample |> List.map (fun (n, v) -> n + " = " + v) |> String.concat ", ") |> ignore
    match d.Reason with
    | Some r when r <> "timeout" && r <> "budget" -> sb.Append("\n    solver: ").Append(r) |> ignore // the message says so
    | _ -> ()
    sb.ToString()

/// The format MSBuild reads, and Visual Studio's error list after it: one line, with a code.
let toBuildText (d: Diagnostic) =
    let text = (toText d).Replace("\r", "").Replace("\n    ", "; ").Replace("\n", " ")
    let head = d.File + "(" + string d.Span.Start.Line + "," + string d.Span.Start.Col + "): " + severityText d.Severity + ": "
    d.File + "(" + string d.Span.Start.Line + "," + string d.Span.Start.Col + "): " + severityText d.Severity + " " + buildCode d + ": "
    + text.Substring head.Length

/// One diagnostic as a JSON object (the --json format, and the MCP tools).
let writeDiagnostic (w: Utf8JsonWriter) (d: Diagnostic) =
    w.WriteStartObject()
    w.WriteString("file", d.File)
    match d.Fn with
    | Some f -> w.WriteString("fn", f)
    | None -> ()
    w.WriteNumber("line", d.Span.Start.Line)
    w.WriteNumber("col", d.Span.Start.Col)
    w.WriteNumber("endLine", d.Span.End.Line)
    w.WriteNumber("endCol", d.Span.End.Col)
    w.WriteString("kind", d.Kind)
    w.WriteString("status", d.Status)
    w.WriteString("severity", severityText d.Severity)
    match d.Property with
    | Some p -> w.WriteString("property", p)
    | None -> ()
    if not d.Counterexample.IsEmpty then
        w.WriteStartObject(if d.Kind = "completeness" then "witness" else "counterexample")
        for (n, v) in d.Counterexample do
            w.WriteString(n, v)
        w.WriteEndObject()
    d.Evidence |> Option.iter (fun e -> w.WriteString("evidence", e))
    d.Reason |> Option.iter (fun r -> w.WriteString("reason", r))
    w.WriteString("message", d.Message)
    w.WriteEndObject()

let toJson (ds: Diagnostic list) =
    use ms = new MemoryStream()
    // Relaxed escaping: keep ' and < > readable for agents (the output is not embedded in HTML).
    let options = JsonWriterOptions(Indented = true, Encoder = Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping)
    (use w = new Utf8JsonWriter(ms, options)
     w.WriteStartArray()
     for d in ds do
         writeDiagnostic w d
     w.WriteEndArray())
    Encoding.UTF8.GetString(ms.ToArray())
