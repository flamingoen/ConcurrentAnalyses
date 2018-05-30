module IntegerAnalysis

open Defines
open ProgramGraphs

let varsIn state = Set.fold (fun rst (x,s) -> Set.add x rst ) Set.empty state

let rec basic state = function
    | []        -> [Set.empty]
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,e) -> x=var ) state
        Set.fold (fun rst elem ->
            List.fold (fun rst' subset -> (Set.add elem subset)::rst' ) [] (basic extract xs)@rst
        ) [] varSet

let boolFilter bFunc b state =
    let basicList = basic state (Set.toList (varsIn state))
    List.fold (fun rst state' ->
        if (Set.contains True (bFunc state' b)) then state' + rst
        else rst
    ) Set.empty basicList
