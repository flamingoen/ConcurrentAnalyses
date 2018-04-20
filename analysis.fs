module Analysis

open Defines
open ProgramGraphs
open WorklistAlgorithm
open BitVectorAnalyses
open ConstraintAnalysis
open SignAnalysis
open IntervalAnalysis

let E_initial ex    = List.fold (fun rst (qs,qt,id) -> (qs,id)::rst ) [] ex
let E_final ex      = List.fold (fun rst (qs,qt,id) -> (qt,id)::rst ) [] ex
let printFooter G   = printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes G)) (List.length G)

let reachingDefinition G ex non =
    printf"\nReaching definition:"
    let res = MFP (L_RD G) G (E_initial ex) (exVal_RD G non) (f_RD non) con_RDg con_RDa
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2,s) -> printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printFooter G

let liveVariables G ex =
    printf"\nLive variables:"
    let res = MFP L_LV (inverse G) (E_final ex) exVal_LV f_LV con_LVg con_LVa
    printfn("\n")
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,s) -> printf("%s " ) x) state)
        printfn("")
        ) res
    printFooter G

let rec condenseState state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o,cstr) -> x=var ) state
        let conVarSet = Set.fold (fun rst (x,sign,o,cstr) -> Set.add (x,sign) rst ) Ø varSet
        Set.add (var,(Set.foldBack (fun (x,s) rst -> if rst="" then s+rst else s+","+rst ) conVarSet  "")) (condenseState extract xs)
let detectionOfSignsAnalysis G ex =
    printfn"\nDetection of signs analysis"
    let f = f_CS (Ls G) (Lc G)
    let res = MFP (Lcs G) G (E_initial ex) (exVal_CS G) f (con_CSg (Lc G)) con_CSa
    printfn "\n"
    let colRes = Map.fold (fun rst q (s,c) ->
        Map.add q ( condenseState s (Set.toList (varsIn s)) , c) rst ) Map.empty res
    Map.iter (fun q (state,c) ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s " ) x s) state
        printfn("")
        ) colRes
    printFooter G

let rec mergeIntervals state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o,cstr) -> x=var ) state
        let conVarSet = Set.fold (fun rst (v,i,o,c) -> Set.add (v,i) rst ) Ø varSet
        Set.add (var,(Set.fold (fun rst (v,i) -> rst+i ) Empty conVarSet)) (mergeIntervals extract xs)
let intervalToString i =
    match i with
    | Undefined  -> "Err"
    | Empty      -> "?"
    | I(max,min) when max=MAX && min=MIN -> "( -∞ : ∞ )"
    | I(max,min) when max=MAX            -> "( "+(string min)+" : ∞ )"
    | I(max,min) when min=MIN            -> "( ∞ : "+(string max)+" )"
    | I(max,min)                         -> "( "+(string min)+" : "+(string max)+" )"
let intervalAnalysis G ex =
    printfn"\nInterval analysis"
    let Li = ((btm_I G),(top_I G),order_I)
    let res = MFP (L_I G) G (E_initial ex) (exVal_I G) (f_I Li (Lc G)) (con_Ig (Lci ob_I G)) con_Ia
    let conRes = Map.fold (fun rst q (s,c) ->
        Map.add q ( mergeIntervals s (Set.toList (varsIn s)) , c) rst ) Map.empty res
    printfn "\n"
    Map.iter (fun q (state,c) ->
        printf("q%-5A\t") q
        Set.iter (fun (x,i) -> printf("%5s-> %-12s" ) x (intervalToString i) ) state
        printf("\t[")
        Set.iter (fun e -> printf("%A") e ) c
        printfn("] ")
        ) conRes
    printFooter G
