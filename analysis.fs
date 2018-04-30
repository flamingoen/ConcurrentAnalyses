module Analysis

open Defines
open ProgramGraphs
open WorklistAlgorithm
open BitVectorAnalyses
open ConstraintAnalysis
open SignAnalysis
open IntervalAnalysis
open ParityAnalysis

let E_initial ex    = List.fold (fun rst (qs,qt,id) -> (qs,id)::rst ) [] ex
let E_final ex      = List.fold (fun rst (qs,qt,id) -> (qt,id)::rst ) [] ex
let printFooter G  =
    printf"\nTransitions taken: %A    " transitions
    printf"Max worklist size: %A    " maxWSize
    printf"Nodes: %i    " (Set.count (allNodes G))
    printfn"Transitions: %i    " (List.length G)
let printPolicy p sat =
    printf"\nPolicies: "
    List.iter (fun policy -> printf("%s ") (policyToString policy) ) p
    printf"\nUnknown in:\t"
    Map.iter(fun q b -> if b then (printf"%A " q) else printf"" ) sat
    printf"\nUnsatified in:\t"
    Map.iter(fun q b -> if b then (printf"") else (printf"%A " q) ) sat
    printfn""


let reachingDefinition G ex non =
    printf"\nReaching definition:"
    let (res,p) = MFP (L_RD G) G (E_initial ex) (exVal_RD G non) (f_RD non) con_RDg con_RDa p_true
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2,s) -> printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printFooter G

let liveVariables G ex =
    printf"\nLive variables:"
    let (res,p) = MFP L_LV (inverse G) (E_final ex) exVal_LV f_LV con_LVg con_LVa p_true
    printfn("\n")
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,s) -> printf("%s " ) x) state)
        printfn("")
        ) res
    printFooter G

let rec condenseState err toString state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o,cstr) -> x=var ) state
        let conVarSet = Set.fold (fun rst (x,sign,o,cstr) -> Set.add (x,sign) rst ) Ø varSet
        Set.add (var,(Set.foldBack (fun (x,s) rst ->
            match s with
            | e when e=err      -> "err."
            | _ when rst="err." -> rst
            | _ when rst=""     -> (toString s)+rst
            | _                 -> (toString s)+","+rst ) conVarSet  "")) (condenseState err toString extract xs)
let detectionOfSignsAnalysis G p ex =
    printfn"\nDetection of signs analysis"
    let f = f_CS ((Ls G),(Lc G))
    let policySatisfied = p_s p
    let (res,sat) = MFP (Lcs G) G (E_initial ex) (exVal_CS G p) f (con_CSg (Lc G)) con_CSa policySatisfied
    printfn "\n"
    let colRes = Map.fold (fun rst q (s,c) ->
        Map.add q ( condenseState S_Undefined signToString s (Set.toList (varsIn s)) , c) rst ) Map.empty res
    Map.iter (fun q (state,c) ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s " ) x s) state
        printfn("")
        ) colRes
    printFooter G
    printPolicy p sat

let rec mergeIntervals state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o,cstr) -> x=var ) state
        let conVarSet = Set.fold (fun rst (v,i,o,c) -> Set.add (v,i) rst ) Ø varSet
        Set.add (var,(Set.fold (fun rst (v,i) -> rst+i ) Empty conVarSet)) (mergeIntervals extract xs)
let intervalAnalysis G p ex =
    printfn"\nInterval analysis"
    let Li = ((btm_I G),(top_I G),order_I)
    let policySatisfied = p_I p
    let (res,sat) = MFP (L_I G) G (E_initial ex) (exVal_I G p) (f_I MAX (Li,(Lc G))) (con_Ig (Lci ob_I G)) con_Ia policySatisfied
    let conRes = Map.fold (fun rst q (s,c) ->
        Map.add q ( mergeIntervals s (Set.toList (varsIn s)) , c) rst ) Map.empty res
    printfn "\n"
    Map.iter (fun q (state,c) ->
        printf("q%-5A\t") q
        Set.iter (fun (x,i) -> printf("%5s-> %-12s" ) x (intervalToString i) ) state
        printfn""
        ) conRes
    printFooter G
    printPolicy p sat


let parityAnalysis G p ex =
    printfn"\n Parity analysis"
    let f = f_p ((Lp G),(Lc G))
    let policySatisfied = p_p p
    let (res,sat) = MFP (Lpc G) G (E_initial ex) (exVal_p G p) f (con_pg (Lcp G)) con_pa policySatisfied
    printfn "\n"
    let colRes = Map.fold (fun rst q (s,c) ->
        Map.add q ( condenseState P_Undefined parityToString s (Set.toList (varsIn s)) , c) rst ) Map.empty res
    Map.iter (fun q (state,c) ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5A " ) x s) state
        printfn("")
        ) colRes
    printFooter G
    printPolicy p sat
