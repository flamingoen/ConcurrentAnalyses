module TablesSign
open Defines

let plus = function
    | Neg,Neg -> Set.ofList [Neg]
    | Neg,Zero -> Set.ofList [Neg]
    | Neg,Pos -> Set.ofList [Neg; Zero; Pos]
    | Zero,Neg -> Set.ofList [Neg]
    | Zero,Zero -> Set.ofList [Zero]
    | Zero,Pos -> Set.ofList [Pos]
    | Pos,Neg -> Set.ofList [Neg; Zero; Pos]
    | Pos,Zero -> Set.ofList [Pos]
    | Pos,Pos -> Set.ofList [Pos]

let multi = function
    | Neg,Neg -> Set.ofList [Pos]
    | Neg,Zero -> Set.ofList [Zero]
    | Neg,Pos -> Set.ofList [Neg]
    | Zero,Neg -> Set.ofList [Zero]
    | Zero,Zero -> Set.ofList [Zero]
    | Zero,Pos -> Set.ofList [Zero]
    | Pos,Neg -> Set.ofList [Neg]
    | Pos,Zero -> Set.ofList [Zero]
    | Pos,Pos -> Set.ofList [Pos]

let modulo = function
    | Neg,Neg -> Set.ofList [Neg;Zero]
    | Neg,Zero -> Set.empty
    | Neg,Pos -> Set.ofList [Pos;Zero]
    | Zero,Neg -> Set.ofList [Zero]
    | Zero,Zero -> Set.empty
    | Zero,Pos -> Set.ofList [Zero]
    | Pos,Neg -> Set.ofList [Zero;Neg]
    | Pos,Zero -> Set.empty
    | Pos,Pos -> Set.ofList [Pos;Zero]

let minus = function
    | Neg,Neg -> Set.ofList [Neg; Zero; Pos]
    | Neg,Zero -> Set.ofList [Neg]
    | Neg,Pos -> Set.ofList [Neg]
    | Zero,Neg -> Set.ofList [Pos]
    | Zero,Zero -> Set.ofList [Zero]
    | Zero,Pos -> Set.ofList [Neg]
    | Pos,Neg -> Set.ofList [Pos]
    | Pos,Zero -> Set.ofList [Pos]
    | Pos,Pos -> Set.ofList [Neg; Zero; Pos]

let divide = function
    | Neg,Neg -> Set.ofList [Pos]
    | Neg,Zero -> Set.empty
    | Neg,Pos -> Set.ofList [Neg]
    | Zero,Neg -> Set.ofList [Zero]
    | Zero,Zero -> Set.empty
    | Zero,Pos -> Set.ofList [Zero]
    | Pos,Neg -> Set.ofList [Neg]
    | Pos,Zero -> Set.empty
    | Pos,Pos -> Set.ofList [Pos]

let less = function
    | Neg,Neg -> Set.ofList [True; False]
    | Neg,Zero -> Set.ofList [True]
    | Neg,Pos -> Set.ofList [True]
    | Zero,Neg -> Set.ofList [False]
    | Zero,Zero -> Set.ofList [False]
    | Zero,Pos -> Set.ofList [True]
    | Pos,Neg -> Set.ofList [False]
    | Pos,Zero -> Set.ofList [False]
    | Pos,Pos -> Set.ofList [True; False]

let lessEq = function
    | Neg,Neg -> Set.ofList [True; False]
    | Neg,Zero -> Set.ofList [True]
    | Neg,Pos -> Set.ofList [True]
    | Zero,Neg -> Set.ofList [True]
    | Zero,Zero -> Set.ofList [True]
    | Zero,Pos -> Set.ofList [False]
    | Pos,Neg -> Set.ofList [False]
    | Pos,Zero -> Set.ofList [False]
    | Pos,Pos -> Set.ofList [True; False]

let greater = function
    | Neg,Neg -> Set.ofList [True; False]
    | Neg,Zero -> Set.ofList [False]
    | Neg,Pos -> Set.ofList [False]
    | Zero,Neg -> Set.ofList [True]
    | Zero,Zero -> Set.ofList [False]
    | Zero,Pos -> Set.ofList [False]
    | Pos,Neg -> Set.ofList [True]
    | Pos,Zero -> Set.ofList [True]
    | Pos,Pos -> Set.ofList [True; False]

let greaterEq = function
    | Neg,Neg -> Set.ofList [True; False]
    | Neg,Zero -> Set.ofList [False]
    | Neg,Pos -> Set.ofList [False]
    | Zero,Neg -> Set.ofList [True]
    | Zero,Zero -> Set.ofList [True]
    | Zero,Pos -> Set.ofList [False]
    | Pos,Neg -> Set.ofList [True]
    | Pos,Zero -> Set.ofList [True]
    | Pos,Pos -> Set.ofList [True; False]

let equal = function
    | Neg,Neg -> Set.ofList [True; False]
    | Neg,Zero -> Set.ofList [False]
    | Neg,Pos -> Set.ofList [False]
    | Zero,Neg -> Set.ofList [False]
    | Zero,Zero -> Set.ofList [True]
    | Zero,Pos -> Set.ofList [False]
    | Pos,Neg -> Set.ofList [False]
    | Pos,Zero -> Set.ofList [False]
    | Pos,Pos -> Set.ofList [True; False]

let notEqual = function
    | Neg,Neg -> Set.ofList [True; False]
    | Neg,Zero -> Set.ofList [True]
    | Neg,Pos -> Set.ofList [True]
    | Zero,Neg -> Set.ofList [True]
    | Zero,Zero -> Set.ofList [False]
    | Zero,Pos -> Set.ofList [True]
    | Pos,Neg -> Set.ofList [True]
    | Pos,Zero -> Set.ofList [True]
    | Pos,Pos -> Set.ofList [True; False]

let _and = function
    | True,True -> Set.ofList [True]
    | True,False -> Set.ofList [False]
    | False,True -> Set.ofList [False]
    | False,False -> Set.ofList [False]
    | _       -> failwith("wrong sign detected") ;;

let _or = function
    | True,True -> Set.ofList [True]
    | True,False -> Set.ofList [True]
    | False,True -> Set.ofList [True]
    | False,False -> Set.ofList [False]
    | _       -> failwith("wrong sign detected") ;;

let _not = function
    | True -> Set.ofList [False]
    | False -> Set.ofList [True]
    | _   -> failwith("wrong sign detected") ;;
