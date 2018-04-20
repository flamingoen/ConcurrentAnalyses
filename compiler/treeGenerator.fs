module TreeGenerator

open Microsoft.FSharp.Text.Lexing
open GuardedCommandParser
open GuardedCommandLexer

let parse input =
    let lexbuf = LexBuffer<_>.FromString input
    GuardedCommandParser.start GuardedCommandLexer.tokenize lexbuf
    ;;
