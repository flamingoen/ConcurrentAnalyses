module tablesSign
open GC

let plus = function
    | "-","-" -> Set.ofList ["-"]
    | "-","0" -> Set.ofList ["-"]
    | "-","+" -> Set.ofList ["-"; "0"; "+"]
    | "0","-" -> Set.ofList ["-"]
    | "0","0" -> Set.ofList ["0"]
    | "0","+" -> Set.ofList ["+"]
    | "+","-" -> Set.ofList ["-"; "0"; "+"]
    | "+","0" -> Set.ofList ["+"]
    | "+","+" -> Set.ofList ["+"]
    | _       -> failwith("wrong sign detected")

let multi = function
    | "-","-" -> Set.ofList ["+"]
    | "-","0" -> Set.ofList ["0"]
    | "-","+" -> Set.ofList ["-"]
    | "0","-" -> Set.ofList ["0"]
    | "0","0" -> Set.ofList ["0"]
    | "0","+" -> Set.ofList ["0"]
    | "+","-" -> Set.ofList ["-"]
    | "+","0" -> Set.ofList ["0"]
    | "+","+" -> Set.ofList ["+"]
    | _       -> failwith("wrong sign detected")

let minus = function
    | "-","-" -> Set.ofList ["-"; "0"; "+"]
    | "-","0" -> Set.ofList ["-"]
    | "-","+" -> Set.ofList ["-"]
    | "0","-" -> Set.ofList ["+"]
    | "0","0" -> Set.ofList ["0"]
    | "0","+" -> Set.ofList ["-"]
    | "+","-" -> Set.ofList ["+"]
    | "+","0" -> Set.ofList ["+"]
    | "+","+" -> Set.ofList ["-"; "0"; "+"]
    | _       -> failwith("wrong sign detected")

let divide = function
    | "-","-" -> Set.ofList ["+"]
    | "-","0" -> Set.empty
    | "-","+" -> Set.ofList ["-"]
    | "0","-" -> Set.ofList ["0"]
    | "0","0" -> Set.empty
    | "0","+" -> Set.ofList ["0"]
    | "+","-" -> Set.ofList ["-"]
    | "+","0" -> Set.empty
    | "+","+" -> Set.ofList ["+"]
    | _       -> failwith("wrong sign detected")

let less = function
    | "-","-" -> Set.ofList [True; False]
    | "-","0" -> Set.ofList [True]
    | "-","+" -> Set.ofList [True]
    | "0","-" -> Set.ofList [False]
    | "0","0" -> Set.ofList [False]
    | "0","+" -> Set.ofList [True]
    | "+","-" -> Set.ofList [False]
    | "+","0" -> Set.ofList [False]
    | "+","+" -> Set.ofList [True; False]
    | _       -> failwith("wrong sign detected") ;;

let lessEq = function
    | "-","-" -> Set.ofList [True; False]
    | "-","0" -> Set.ofList [True]
    | "-","+" -> Set.ofList [True]
    | "0","-" -> Set.ofList [True]
    | "0","0" -> Set.ofList [True]
    | "0","+" -> Set.ofList [False]
    | "+","-" -> Set.ofList [False]
    | "+","0" -> Set.ofList [False]
    | "+","+" -> Set.ofList [True; False]
    | _       -> failwith("wrong sign detected") ;;

let greater = function
    | "-","-" -> Set.ofList [True; False]
    | "-","0" -> Set.ofList [False]
    | "-","+" -> Set.ofList [False]
    | "0","-" -> Set.ofList [True]
    | "0","0" -> Set.ofList [False]
    | "0","+" -> Set.ofList [False]
    | "+","-" -> Set.ofList [True]
    | "+","0" -> Set.ofList [True]
    | "+","+" -> Set.ofList [True; False]
    | _       -> failwith("wrong sign detected") ;;

let greaterEq = function
    | "-","-" -> Set.ofList [True; False]
    | "-","0" -> Set.ofList [False]
    | "-","+" -> Set.ofList [False]
    | "0","-" -> Set.ofList [True]
    | "0","0" -> Set.ofList [True]
    | "0","+" -> Set.ofList [False]
    | "+","-" -> Set.ofList [True]
    | "+","0" -> Set.ofList [True]
    | "+","+" -> Set.ofList [True; False]
    | _       -> failwith("wrong sign detected") ;;

let equal = function
    | "-","-" -> Set.ofList [True; False]
    | "-","0" -> Set.ofList [False]
    | "-","+" -> Set.ofList [False]
    | "0","-" -> Set.ofList [False]
    | "0","0" -> Set.ofList [True]
    | "0","+" -> Set.ofList [False]
    | "+","-" -> Set.ofList [False]
    | "+","0" -> Set.ofList [False]
    | "+","+" -> Set.ofList [True; False]
    | _       -> failwith("wrong sign detected") ;;

let notEqual = function
    | "-","-" -> Set.ofList [True; False]
    | "-","0" -> Set.ofList [True]
    | "-","+" -> Set.ofList [True]
    | "0","-" -> Set.ofList [True]
    | "0","0" -> Set.ofList [False]
    | "0","+" -> Set.ofList [True]
    | "+","-" -> Set.ofList [True]
    | "+","0" -> Set.ofList [True]
    | "+","+" -> Set.ofList [True; False]
    | _       -> failwith("wrong sign detected") ;;

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
