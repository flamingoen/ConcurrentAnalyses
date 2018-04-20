module ConstraintAnalysis

open Lattice
open ProgramGraphs
open GC

let varsIn state = Set.fold (fun rst (x,sign,o,c) -> Set.add x rst ) Set.empty state

let rec basic state = function
    | []        -> [Set.empty]
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,e,o,c) -> x=var ) state
        Set.fold (fun rst elem ->
            List.fold (fun rst' subset -> (Set.add elem subset)::rst' ) [] (basic extract xs)@rst
        ) [] varSet

let boolFilter bFunc b state =
    let basicList = basic state (Set.toList (varsIn state))
    List.fold (fun rst state' ->
        if (Set.contains True (bFunc state' b)) then state' + rst
        else rst
    ) Set.empty basicList

let removeOrigin set = Set.fold (fun rst (v,s,o,c) -> Set.add (v,s) rst ) Set.empty set
let removeConcurrent set = removeOrigin (Set.filter (fun (v,s,o,c) -> (not (o=Concurrent)) ) set)

let exVal_C = Ø

let btm_C G = Set.fold (fun rst var -> (Set.ofList [(var,"0");(var,"+");(var,"-");(var,"T")]) + rst ) Ø (varsInGraph G)

let btm_Ci G i = Set.fold (fun rst var -> Set.add (var,i) rst ) Ø (varsInGraph G)

let Lci i G =
    let order s1 s2 = Set.intersect s1 s2
    ((btm_Ci G i),Ø,order)

let Lc G =
    let order s1 s2 = Set.intersect s1 s2
    ((btm_C G),Ø,order)

let con_Cg id s1 s2 c = Map.find id c
let con_Ca id s1 s2 c =
    let filtered = Set.filter (fun (v,s,o) -> o=Global ) (Set.union s1 s2)
    let s' =  Set.fold (fun rst (v,s,o) -> Set.add (v,s,Concurrent) rst ) Set.empty filtered
    match Map.tryFind id c with
        | Some(s) -> Map.add id (s'+s) c
        | None    -> Map.add id s' c

let f_C bFunc Ls Lc Ss Sc (qs,a,qt,id) =
    match a with
    | Node( b, _ ) when isBoolOp b ->
        let vars = varsInA a
        let filtered = Set.filter (fun (x,s) -> (Set.contains x vars)) (removeOrigin (boolFilter bFunc a (top Ls) ) )
        (filtered - (removeConcurrent Ss)) + Sc
    | _ -> Sc
