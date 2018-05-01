module PolicyGenerator

open Microsoft.FSharp.Text.Lexing
open PoliciesParser
open PoliciesLexer

let parsePolicy input =
    let lexbuf = LexBuffer<_>.FromString input
    PoliciesParser.policy PoliciesLexer.tokenize lexbuf
