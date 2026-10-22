/// Diagnostics shared by every stage: one record, printed for humans or written as JSON.
/// JSON is written with Utf8JsonWriter by hand: no reflection, so it works under Native AOT.
module Quod.Diagnostics

open System.IO
open System.Text
open System.Text.Json
open Quod.Syntax

type Severity =
    | Error
    | Warning

type Diagnostic =
    { File: string
      Span: Span
      /// syntax | type | proof | completeness
      Kind: string
      /// error | refuted | underspecified | inconclusive
      Status: string
      Severity: Severity
      Fn: string option
      Property: string option
      /// Values of the parameters that make a proof obligation fail (name, Quod value).
      Counterexample: (string * string) list
      Message: string }

/// Raised by a stage that stops at its first error (the parser does in 0.1).
exception QuodError of Diagnostic

let syntaxError (file: string) (span: Span) (message: string) =
    QuodError
        { File = file; Span = span; Kind = "syntax"; Status = "error"; Severity = Error
          Fn = None; Property = None; Counterexample = []; Message = message }

let private severityText = function Error -> "error" | Warning -> "warning"

/// `file(line,col): error: message`, the format editors and agents already recognise.
let toText (d: Diagnostic) =
    let sb = StringBuilder()
    sb.Append(d.File).Append('(').Append(d.Span.Start.Line).Append(',').Append(d.Span.Start.Col)
      .Append("): ").Append(severityText d.Severity).Append(": ") |> ignore
    match d.Fn with
    | Some f -> sb.Append("in ").Append(f).Append(": ") |> ignore
    | None -> ()
    sb.Append(d.Message) |> ignore
    if not d.Counterexample.IsEmpty then
        sb.Append("\n    counterexample: ").Append(d.Counterexample |> List.map (fun (n, v) -> n + " = " + v) |> String.concat ", ") |> ignore
    sb.ToString()

let private writeOne (w: Utf8JsonWriter) (d: Diagnostic) =
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
        w.WriteStartObject("counterexample")
        for (n, v) in d.Counterexample do
            w.WriteString(n, v)
        w.WriteEndObject()
    w.WriteString("message", d.Message)
    w.WriteEndObject()

let toJson (ds: Diagnostic list) =
    use ms = new MemoryStream()
    // Relaxed escaping: keep ' and < > readable for agents (the output is not embedded in HTML).
    let options = JsonWriterOptions(Indented = true, Encoder = Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping)
    (use w = new Utf8JsonWriter(ms, options)
     w.WriteStartArray()
     for d in ds do
         writeOne w d
     w.WriteEndArray())
    Encoding.UTF8.GetString(ms.ToArray())
