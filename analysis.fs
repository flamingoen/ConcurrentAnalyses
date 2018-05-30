module Analysis

open Defines
open ProgramGraphs
open WorklistAlgorithm
open BitVectorAnalyses
open IntegerAnalysis
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
    let res = MFPc (L_RD G) G (E_initial ex) (exVal_RD G non) f_RD con_BVFg (con_RDa)
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2) -> if q1=non then printf("%s: ?\t\t " ) x else printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printFooter G

let liveVariables G ex =
    printf"\nLive variables:"
    let res = MFPc L_LV (inverse G) (E_final ex) exVal_LV f_LV con_BVFg (con_LVa)
    printfn("\n")
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun x -> printf("%s " ) x) state)
        printfn("")
        ) res
    printFooter G

let rec condenseState err toString state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs) -> x=var ) state
        Set.add (var,(Set.foldBack (fun (x,s) rst ->
            match s with
            | e when e=err      -> "err."
            | _ when rst="err." -> rst
            | _ when rst=""     -> (toString s)+rst
            | _                 -> (toString s)+","+rst ) varSet  "")) (condenseState err toString extract xs)
let detectionOfSignsAnalysis G p ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (Ls G) G) G (E_initial ex) (exVal_C (exVal_s G p)) (Fc f_s Bs)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printFooter G
    printfn"\nDetection of signs analysis"
    let (res,sat) = MFPp (Ls G) G (E_initial ex) (exVal_s G p) f_s (con_sg Cs') (con_sa Cs') (p_s p)
    let colRes = Map.fold (fun r q s ->
        Map.add q ( condenseState S_Undefined signToString s (Set.toList (varsIn s))) r ) Map.empty res
    printfn""
    Map.iter (fun q state ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s " ) x s) state
        printfn("")
        ) colRes
    printFooter G
    printPolicy p sat

let rec mergeIntervals state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs) -> x=var ) state
        Set.add (var,(Set.fold (fun rst (v,i) -> rst+i ) Empty varSet)) (mergeIntervals extract xs)
let intervalAnalysis G p ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (L_I G) G) G (E_initial ex) (exVal_C (exVal_I G p)) (Fc (f_I MAX) B_I)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printfn"\nInterval analysis"
    let (res,sat) = MFPp (L_I G) G (E_initial ex) (exVal_I G p) (f_I MAX) (con_ig Cs') (con_ia Cs') (p_I p)
    let conRes = Map.fold (fun rst q s -> Map.add q ( mergeIntervals s (Set.toList (varsIn s))) rst ) Map.empty res
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%-5A\t") q
        Set.iter (fun (x,i) -> printf("%5s-> %-12s" ) x (intervalToString i) ) state
        printfn""
        ) conRes
    printFooter G
    printPolicy p sat


let parityAnalysis G p ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (Lp G) G) G (E_initial ex) (exVal_C (exVal_p G p)) (Fc f_p Bp)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printfn"\n Parity analysis"
    let (res,sat) = MFPp (Lp G) G (E_initial ex) (exVal_p G p) f_p con_pg (con_pa Cs') (p_p p)
    printfn "\n"
    let colRes = Map.fold (fun rst q s ->
        Map.add q ( condenseState P_Undefined parityToString s (Set.toList (varsIn s))) rst ) Map.empty res
    Map.iter (fun q state ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5A " ) x s) state
        printfn("")
        ) colRes
    printFooter G
    printPolicy p sat
