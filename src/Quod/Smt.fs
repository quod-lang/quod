/// Talking to Z3: one persistent `z3 -in` process per compilation, driven in SMT-LIB text with
/// push/pop, plus a small S-expression reader for its answers (models, values).
module Quod.Smt

open System
open System.Diagnostics
open System.IO
open System.Text

// --- S-expressions --------------------------------------------------------------------

type SExpr =
    | Atom of string
    | List of SExpr list

let parseSExprs (text: string) : SExpr list =
    let mutable i = 0
    let n = text.Length
    let rec skip () =
        while i < n && Char.IsWhiteSpace text.[i] do
            i <- i + 1
        if i < n && text.[i] = ';' then
            while i < n && text.[i] <> '\n' do
                i <- i + 1
            skip ()
    let rec one () : SExpr =
        skip ()
        if text.[i] = '(' then
            i <- i + 1
            let items = ResizeArray<SExpr>()
            skip ()
            while i < n && text.[i] <> ')' do
                items.Add(one ())
                skip ()
            i <- i + 1
            List(List.ofSeq items)
        elif text.[i] = '"' then
            let start = i
            i <- i + 1
            while i < n && not (text.[i] = '"' && (i + 1 >= n || text.[i + 1] <> '"')) do
                i <- i + (if text.[i] = '"' then 2 else 1)
            i <- i + 1
            Atom(text.Substring(start, i - start))
        elif text.[i] = '|' then
            let start = i
            i <- i + 1
            while i < n && text.[i] <> '|' do
                i <- i + 1
            i <- i + 1
            Atom(text.Substring(start + 1, i - start - 2))
        else
            let start = i
            while i < n && not (Char.IsWhiteSpace text.[i]) && text.[i] <> '(' && text.[i] <> ')' do
                i <- i + 1
            Atom(text.Substring(start, i - start))
    let out = ResizeArray<SExpr>()
    skip ()
    while i < n do
        out.Add(one ())
        skip ()
    List.ofSeq out

let rec sexprText (e: SExpr) =
    match e with
    | Atom a -> a
    | List xs -> "(" + (xs |> List.map sexprText |> String.concat " ") + ")"

// --- the Z3 process -------------------------------------------------------------------

type CheckResult =
    | Sat
    | Unsat
    | Unknown of reason: string

exception SmtFailure of string

/// Where to find z3: an explicit path, next to the quod binary, QUOD_Z3, then PATH.
let findZ3 (explicitPath: string option) : string option =
    let exe = if OperatingSystem.IsWindows() then "z3.exe" else "z3"
    let candidates =
        [ yield! Option.toList explicitPath
          yield Path.Combine(AppContext.BaseDirectory, exe)
          match Environment.GetEnvironmentVariable "QUOD_Z3" with
          | null | "" -> ()
          | p -> yield p
          match Environment.GetEnvironmentVariable "PATH" with
          | null -> ()
          | path ->
              for dir in path.Split(Path.PathSeparator) do
                  if dir <> "" then yield Path.Combine(dir, exe) ]
    candidates |> List.tryFind File.Exists

/// A running `z3 -in` process. Commands are written as SMT-LIB text; answers are read back
/// as balanced S-expressions. `log` receives every command, to replay a session by hand.
type Session(z3Path: string, timeoutMs: int, log: TextWriter option) =
    let psi = ProcessStartInfo(z3Path, "-in -smt2")
    do
        psi.RedirectStandardInput <- true
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.UseShellExecute <- false
    let proc = Process.Start psi
    let input = proc.StandardInput
    let output = proc.StandardOutput

    /// Read one complete answer: an atom line, or a parenthesised block spanning lines.
    let readAnswer () : string =
        let sb = StringBuilder()
        let mutable depth = 0
        let mutable started = false
        let mutable fin = false
        while not fin do
            let line = output.ReadLine()
            if isNull line then raise (SmtFailure("z3 stopped unexpectedly: " + proc.StandardError.ReadToEnd()))
            let t = line.Trim()
            if t <> "" then
                sb.AppendLine(line) |> ignore
                for ch in line do
                    if ch = '(' then
                        depth <- depth + 1
                        started <- true
                    elif ch = ')' then depth <- depth - 1
                if depth <= 0 then fin <- true
        let answer = sb.ToString().Trim()
        if answer.StartsWith "(error" then raise (SmtFailure("z3 rejected a command: " + answer))
        answer

    do
        input.AutoFlush <- false

    /// The commands of the current context, one list per push level, kept to replay it. A check
    /// that fails in incremental mode is tried again on a fresh solver: (reset), then the whole
    /// context. The two modes succeed on different queries: in incremental mode (after a push)
    /// Z3 skips part of its preprocessing, and some quantified proofs that take 1.8 s on a fresh
    /// query answer "unknown"; others are found only incrementally. Trying both proves the union.
    let frames = ResizeArray<ResizeArray<string>>([ ResizeArray<string>() ])
    /// After a fresh retry, z3 holds the flat context: rebuild the push levels before going on
    /// (lazily, so that the model of the retry can still be read).
    let mutable dirty = false

    let raw (command: string) = input.WriteLine command

    let restore () =
        if dirty then
            raw "(reset)"
            for k in 0 .. frames.Count - 1 do
                if k > 0 then raw "(push 1)"
                for command in frames.[k] do raw command
            dirty <- false

    let readResult () =
        input.Flush()
        match readAnswer () with
        | "sat" -> Sat
        | "unsat" -> Unsat
        | "unknown" ->
            raw "(get-info :reason-unknown)"
            input.Flush()
            let r = readAnswer ()
            Unknown(if r.Contains "timeout" || r.Contains "canceled" then "timeout" else r)
        | other -> raise (SmtFailure("unexpected answer from z3: " + other))

    member _.Send(command: string) =
        restore ()
        log |> Option.iter (fun w -> w.WriteLine command)
        frames.[frames.Count - 1].Add command
        raw command

    member private _.Raw(command: string) = raw command

    member s.Init() =
        s.Send "(set-option :print-success false)"
        s.Send "(set-option :produce-models true)"
        // As Dafny does: quantifiers are instantiated by their triggers only (no model-based
        // instantiation). A failing check then answers "unknown" quickly, with a candidate
        // model, instead of searching for an exact model until the time limit.
        s.Send "(set-option :smt.mbqi false)"
        s.Send("(set-option :timeout " + string timeoutMs + ")")
        s.Send "(set-logic ALL)"

    /// Change the time limit of the following checks (milliseconds).
    member s.SetTimeout(ms: int) = s.Send("(set-option :timeout " + string ms + ")")

    /// The time limit given at start, to restore after a temporary change.
    member _.DefaultTimeout = timeoutMs

    member _.Push() =
        restore ()
        log |> Option.iter (fun w -> w.WriteLine "(push 1)")
        frames.Add(ResizeArray<string>())
        raw "(push 1)"

    member _.Pop() =
        restore ()
        log |> Option.iter (fun w -> w.WriteLine "(pop 1)")
        if frames.Count > 1 then
            frames.RemoveAt(frames.Count - 1)
            raw "(pop 1)"

    member s.Check() : CheckResult =
        restore ()
        log |> Option.iter (fun w -> w.WriteLine "(check-sat)")
        raw "(check-sat)"
        readResult ()

    /// Check, and when the answer is unknown, check again on a fresh solver (see frames). For
    /// proof obligations only: a search for a model (completeness) wants the first, quick
    /// "unknown" and its candidate model.
    member s.CheckBoth() : CheckResult =
        match s.Check() with
        | Unknown _ ->
            raw "(reset)"
            for frame in frames do
                for command in frame do raw command
            raw "(check-sat)"
            dirty <- true
            readResult ()
        | r -> r

    /// Values of terms in the current model, as S-expressions.
    member s.Values(terms: string list) : SExpr list =
        if terms.IsEmpty then []
        else
            s.Raw("(get-value (" + String.Join(" ", terms) + "))")
            input.Flush()
            try
                match parseSExprs (readAnswer ()) with
                | [ List pairs ] -> pairs |> List.map (function List [ _; v ] -> v | other -> other)
                | _ -> []
            with SmtFailure _ -> [] // no model available (e.g. after a timeout)

    interface IDisposable with
        member s.Dispose() =
            try
                s.Raw "(exit)"
                input.Flush()
                if not (proc.WaitForExit 2000) then proc.Kill()
            with _ -> ()
            proc.Dispose()
