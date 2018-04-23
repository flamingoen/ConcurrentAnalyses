module Policies
open Defines

type rule = R_Pl | R_Mi | R_Zr
type policy = Policy of (string * rule)
type policies = policy List

let p_true s = true 
