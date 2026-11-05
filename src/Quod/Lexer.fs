/// Turns Quod source text into tokens, each with its span.
module Quod.Lexer

open System
open Quod.Syntax
open Quod.Diagnostics

type TokenKind =
    | TkIdent of string
    | TkInt of bigint
    | TkChar of int
    | TkString of int list
    | TkKeyword of string
    | TkSymbol of string
    | TkEof

type Token = { Kind: TokenKind; Span: Span }

let keywords =
    set [ "fn"; "lemma"; "requires"; "ensures"; "loose"; "decreases"; "invariant"
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
    | TkChar _ -> "a character"
    | TkString _ -> "a string"
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
        elif c = '\'' || c = '"' then
            let start = pos ()
            let quote = c
            let fail (message: string) = raise (syntaxError file (spanOf start (pos ())) message)
            advance 1
            let scalars = ResizeArray<int>()
            while i < src.Length && src.[i] <> quote && src.[i] <> '\n' do
                if src.[i] = '\\' then
                    if i + 1 >= src.Length then fail "a '\\' at the end of the file"
                    let e = src.[i + 1]
                    advance 2
                    match e with
                    | 'n' -> scalars.Add 10
                    | 't' -> scalars.Add 9
                    | 'r' -> scalars.Add 13
                    | '0' -> scalars.Add 0
                    | '\\' -> scalars.Add 92
                    | '\'' -> scalars.Add 39
                    | '"' -> scalars.Add 34
                    | 'u' ->
                        // \u{1F600}
                        if i >= src.Length || src.[i] <> '{' then fail "write a Unicode escape as \\u{1F600}"
                        advance 1
                        let first = i
                        while i < src.Length && Uri.IsHexDigit src.[i] do advance 1
                        if i >= src.Length || src.[i] <> '}' || i = first || i - first > 6 then fail "write a Unicode escape as \\u{1F600}, with 1 to 6 hexadecimal digits"
                        let v = Convert.ToInt32(src.Substring(first, i - first), 16)
                        advance 1
                        if v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF) then fail "this escape is not a Unicode scalar value (0 to 10FFFF, without D800 to DFFF)"
                        scalars.Add v
                    | other -> fail ("unknown escape '\\" + string other + "': the escapes are \\n \\t \\r \\0 \\\\ \\' \\\" \\u{...}")
                elif Char.IsHighSurrogate src.[i] && i + 1 < src.Length && Char.IsLowSurrogate src.[i + 1] then
                    scalars.Add(Char.ConvertToUtf32(src.[i], src.[i + 1]))
                    advance 2
                elif Char.IsSurrogate src.[i] then
                    fail "a lone surrogate is not a character"
                else
                    scalars.Add(int src.[i])
                    advance 1
            if i >= src.Length || src.[i] <> quote then
                fail (if quote = '"' then "this string is not closed on its line" else "this character is not closed on its line")
            advance 1
            if quote = '"' then
                tokens.Add { Kind = TkString(List.ofSeq scalars); Span = spanOf start (pos ()) }
            else
                if scalars.Count <> 1 then fail "a character literal holds one character: use \" for a string"
                tokens.Add { Kind = TkChar scalars.[0]; Span = spanOf start (pos ()) }
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
                    | _ -> ""
                raise (syntaxError file (spanOf start (pos ())) ("unexpected character '" + string c + "'" + hint))
    let here = pos ()
    tokens.Add { Kind = TkEof; Span = spanOf here here }
    List.ofSeq tokens
