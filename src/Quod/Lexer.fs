/// Turns Quod source text into tokens, each with its span.
module Quod.Lexer

open System
open Quod.Syntax
open Quod.Diagnostics

type TokenKind =
    | TkIdent of string
    | TkInt of bigint
    | TkKeyword of string
    | TkSymbol of string
    | TkEof

type Token = { Kind: TokenKind; Span: Span }

let keywords =
    set [ "fn"; "requires"; "ensures"; "loose"; "decreases"; "invariant"
          "let"; "mut"; "if"; "else"; "while"; "assert"; "return"
          "forall"; "exists"; "in"; "true"; "false"; "result"
          "int"; "nat"; "bool"; "seq" ]

/// Longest first: `<==>` before `<=`, `==>` before `==`, `->` before `-`, `..` before `.`.
let private symbols =
    [ "<==>"; "==>"; "=="; "!="; "<="; ">="; "&&"; "||"; "->"; "=>"; ".."
      "("; ")"; "{"; "}"; "["; "]"; "<"; ">"; ","; ":"; ";"; "="
      "+"; "-"; "*"; "/"; "%"; "!"; "." ]

/// A readable name for a token, used in "expected X, found Y" messages.
let describe (k: TokenKind) =
    match k with
    | TkIdent n -> "identifier '" + n + "'"
    | TkInt v -> "number " + v.ToString()
    | TkKeyword k -> "'" + k + "'"
    | TkSymbol s -> "'" + s + "'"
    | TkEof -> "end of file"

let tokenize (file: string) (src: string) : Token list =
    let tokens = ResizeArray<Token>()
    let mutable i = 0
    let mutable line = 1
    let mutable col = 1
    let pos () = { Line = line; Col = col }
    let advance n =
        for _ in 1 .. n do
            if src.[i] = '\n' then
                line <- line + 1
                col <- 1
            else
                col <- col + 1
            i <- i + 1
    let isIdentStart c = Char.IsLetter c || c = '_'
    let isIdentChar c = Char.IsLetterOrDigit c || c = '_'
    while i < src.Length do
        let c = src.[i]
        if c = ' ' || c = '\t' || c = '\r' || c = '\n' then
            advance 1
        elif c = '/' && i + 1 < src.Length && src.[i + 1] = '/' then
            while i < src.Length && src.[i] <> '\n' do
                advance 1
        elif Char.IsDigit c then
            let start = pos ()
            let first = i
            while i < src.Length && Char.IsDigit src.[i] do
                advance 1
            if i < src.Length && isIdentStart src.[i] then
                raise (syntaxError file (spanOf start (pos ())) "a number cannot be followed by a letter")
            tokens.Add { Kind = TkInt(bigint.Parse(src.Substring(first, i - first))); Span = spanOf start (pos ()) }
        elif isIdentStart c then
            let start = pos ()
            let first = i
            while i < src.Length && isIdentChar src.[i] do
                advance 1
            let word = src.Substring(first, i - first)
            let kind = if keywords.Contains word then TkKeyword word else TkIdent word
            tokens.Add { Kind = kind; Span = spanOf start (pos ()) }
        else
            let start = pos ()
            match symbols |> List.tryFind (fun s -> String.CompareOrdinal(src, i, s, 0, s.Length) = 0) with
            | Some s ->
                advance s.Length
                tokens.Add { Kind = TkSymbol s; Span = spanOf start (pos ()) }
            | None ->
                advance 1
                let hint =
                    match c with
                    | '|' -> " (the length of a sequence is written len(s), not |s|)"
                    | '\'' | '"' -> " (Quod 0.1 has no characters or strings yet)"
                    | _ -> ""
                raise (syntaxError file (spanOf start (pos ())) ("unexpected character '" + string c + "'" + hint))
    let here = pos ()
    tokens.Add { Kind = TkEof; Span = spanOf here here }
    List.ofSeq tokens
