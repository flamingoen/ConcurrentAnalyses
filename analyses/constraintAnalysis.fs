module ConstraintAnalysis

open Defines
open ProgramGraphs

let varsIn state = Set.fold (fun rst (x,s,c) -> Set.add x rst ) Set.empty state

let rec basic state = function
    | []        -> [Set.empty]
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,e,c) -> x=var ) state
        Set.fold (fun rst elem ->
            List.fold (fun rst' subset -> (Set.add elem subset)::rst' ) [] (basic extract xs)@rst
        ) [] varSet

let boolFilter bFunc b state =
    let basicList = basic state (Set.toList (varsIn state))
    List.fold (fun rst state' ->
        if (Set.contains True (bFunc state' b)) then state' + rst
        else rst
    ) Set.empty basicList

let rmConstraint set = Set.fold (fun rst (v,s,c) -> Set.add (v,s) Ø ) Ø set

let exVal_C = Ø

let btm_C G = Set.fold (fun rst var -> (Set.ofList [(var,Pos);(var,Neg);(var,Zero)]) + rst ) Ø (varsInGraph G)

let btm_Ci G i = Set.fold (fun rst var -> Set.add (var,i) rst ) Ø (varsInGraph G)

let btm_Cp G = Set.fold (fun rst var -> (Set.ofList [(var,Odd);(var,Even)]) + rst ) Ø (varsInGraph G)

let Lci i G =
    let lob s1 s2 = Set.intersect s1 s2
    let dif s1 s2 = Set.difference s1 s2
    ((btm_Ci G i),Ø,lob,dif)

let Lcp G =
    let order s1 s2 = Set.intersect s1 s2
    let dif s1 s2 = Set.difference s1 s2
    ((btm_Cp G),Ø,lob,dif)

let Lc G =
    let order s1 s2 = Set.intersect s1 s2
    let dif s1 s2 = Set.difference s1 s2
    ((btm_C G),Ø,lob,dif)

let con_Cg id s1 s2 c = Map.find id c
let con_Ca id s1 s2 c =
    let s' =  Set.fold (fun rst (v,s) -> Set.add (v,s) rst ) Set.empty (s2-s1)
    match Map.tryFind id c with
        | Some(s) -> Map.add id (s'+s) c
        | None    -> Map.add id s' c

let f_C bFunc Ls Lc Ss Sc (qs,a,qt,id) =
    match a with
    | Node( b, _ ) when isBoolOp b ->
        let vars = varsInA a
        let filtered = Set.filter (fun (x,s) -> (Set.contains x vars)) (rmConstraint ( boolFilter bFunc a (top Ls) ))
        (filtered - (rmConstraint Ss) + Sc)
    | _ -> Sc
