module Policies
open Defines

type rule = R_Pl | R_Mi | R_Zr | R_Even | R_Odd | R_Grt of int | R_Lt of int | R_Eq of int
type policy = Policy of (string * rule)
type policies = policy List

let p_true s = true

let ruleToString = function
    | R_Pl -> "->+"
    | R_Mi -> "->-"
    | R_Zr -> "->0"
    | R_Odd -> "->odd"
    | R_Even -> "->even"
    | R_Grt(n) -> ">"+(string n)
    | R_Lt(n) -> "<"+(string n)
    | R_Eq(n) -> "="+(string n)

let policyToString = function
    (var,rule) -> var+(ruleToString rule)
