module Policies
open Defines

type rule = R_Pl | R_Mi | R_Zr | R_Even | R_Odd
type policy = Policy of (string * rule)
type policies = policy List

let p_true s = true

let ruleToString = function
    | R_Pl -> "+"
    | R_Mi -> "-"
    | R_Zr -> "0"
    | R_Odd -> "odd"
    | R_Even -> "even"

let policyToString = function
    (var,rule) -> var+"->"+(ruleToString rule)
