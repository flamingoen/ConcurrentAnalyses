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
open CombinatorialAnalysis

let E_initial ex    = List.fold (fun rst (qs,qt,id) -> (qs,id)::rst ) [] ex
let E_final ex      = List.fold (fun rst (qs,qt,id) -> (qt,id)::rst ) [] ex
let printFooter G  =
    printf"\nTransitions taken: %A    " transitions
    printf"Max worklist size: %A    " maxWSize
    printf"Nodes: %i    " (Set.count (allNodes G))
    printfn"Transitions: %i    " (List.length G)
let printPolicy p sat =
    printf"\nPolicies: "
    printfn"%s" (List.fold(fun r p ->
        let s = (List.fold(fun r' policy ->
            if r'="" then (policyToString policy)+r' else (policyToString policy)+" | "+r')
        "" p)
        if r="" then "("+s+")" else "("+s+") & "+r
    ) "" p)
    printf"\n"
    Map.iter(printfn"q%A\t %A") sat


let reachingDefinition G ex non =
    printf"\nReaching definition:"
    let res = MFPc (L_RD G) G (E_initial ex) (exVal_RD G non) f_RD con_BVFg (con_BVFa gen_RD)
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2) -> if q1=non then printf("%s: ?\t\t " ) x else printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printFooter G
let RDtest G ex non = MFPc (L_RD G) G (E_initial ex) (exVal_RD G non) f_RD con_BVFg (con_BVFa gen_RD)

let liveVariables G ex =
    printf"\nLive variables:"
    let res = MFPc L_LV (inverse G) (E_final ex) exVal_LV f_LV con_BVFg (con_BVFa gen_LV)
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
let detectionOfSignsAnalysis G p i ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (Ls G) G) G (E_initial ex) (exVal_C (exVal_s G p)) (Fc f_s Bs)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printfn"\nDetection of signs analysis"
    let (res,sat) = MFPp (Ls G) G (E_initial ex) (exVal_s G i) f_s (con_sg Cs') (con_sa Cs') Map.empty (policySats ruleSatisfied_s p)
    let colRes = Map.fold (fun r q s ->
        Map.add q ( condenseState S_Undefined signToString s (Set.toList (varsIn s))) r ) Map.empty res
    printfn""
    Map.iter (fun q state ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s" ) x s) state
        printfn("")
        ) colRes
    printFooter G
    printPolicy p sat

let dosTest G p ex =
    let Cs = MFP (Lc (Ls G) G) G (E_initial ex) (exVal_C (exVal_s G p)) (Fc f_s Bs)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    MFPp (Ls G) G (E_initial ex) (exVal_s G p) f_s (con_sg Cs') (con_sa Cs') Map.empty (policySats ruleSatisfied_s p)

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
    let (res,sat) = MFPp (L_I G) G (E_initial ex) (exVal_I G p) (f_I MAX) (con_ig Cs') (con_ia Cs') Map.empty (policySats ruleSatisfied_I p)
    let conRes = Map.fold (fun rst q s -> Map.add q ( mergeIntervals s (Set.toList (varsIn s))) rst ) Map.empty res
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%-5A\t") q
        Set.iter (fun (x,i) -> printf("%5s-> %-12s" ) x (intervalToString i) ) state
        printfn""
        ) conRes
    printFooter G
    printPolicy p sat
let doiTest G p ex =
    let Cs = MFP (Lc (L_I G) G) G (E_initial ex) (exVal_C (exVal_I G p)) (Fc (f_I MAX) B_I)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    MFPp (L_I G) G (E_initial ex) (exVal_I G p) (f_I MAX) (con_ig Cs') (con_ia Cs') Map.empty (policySats ruleSatisfied_I p)


let parityAnalysis G p ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (Lp G) G) G (E_initial ex) (exVal_C (exVal_p G p)) (Fc f_p Bp)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printfn"\n Parity analysis"
    let (res,sat) = MFPp (Lp G) G (E_initial ex) (exVal_p G p) f_p con_pg (con_pa Cs') Map.empty (policySats ruleSatisfied_P p)
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
let parTest G p ex =
    let Cs = MFP (Lc (Lp G) G) G (E_initial ex) (exVal_C (exVal_p G p)) (Fc f_p Bp)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    MFPp (Lp G) G (E_initial ex) (exVal_p G p) f_p con_pg (con_pa Cs') Map.empty (policySats ruleSatisfied_P p)

let combinatorialAnalysis (f1,l1,ex1,ca1,cg1,p1) (f2,l2,ex2,ca2,cg2,p2) G p ex =
    let L = (L_cb (l1,l2))
    let exVal = (exVal_cb (ex1,ex2))
    let f = (f_cb f1 f2)
    let Ca = Ca_cb (ca1,ca2)
    let Cg = Cg_cb (cg1,cg2)
    let Ps = P_cb (p1,p2) p
    MFPp L G (E_initial ex) exVal f Cg Ca Map.empty Ps

let parSignAnalysis G p ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (Lp G) G) G (E_initial ex) (exVal_C (exVal_p G p)) (Fc f_p Bp)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printfn"\n Combinational analysis"
    let parityFramework = framework_p Cs' G p
    let signFramework = framework_s Cs' G p
    let (res,sat) = combinatorialAnalysis parityFramework signFramework G p ex
    printfn""
    printMap res
    printFooter G
    printPolicy p sat

let parIntAnalysis G p ex =
    printfn"\nAnalysing constraints"
    let Cs = MFP (Lc (Lp G) G) G (E_initial ex) (exVal_C (exVal_p G p)) (Fc f_p Bp)
    let Cs' = Map.fold (fun r id (s,c) -> Map.add id c r) Map.empty Cs
    printfn"\n Combinational analysis"
    let parityFramework = framework_p Cs' G p
    let intervalFramework = framework_i Cs' G p
    let (res,sat) = combinatorialAnalysis parityFramework intervalFramework G p ex
    printfn""
    Map.iter (fun key s1 ->
        printfn"%A" key
        Set.iter(fun (e1,e2) ->
            if Set.isEmpty e1 then printf" {}" else Set.iter(printf" %A ") e1
            printfn""
            if Set.isEmpty e2 then printf" {}" else Set.iter(printf" %A ") e2
            printfn"\n"
        ) s1
    ) res
    printFooter G
    printPolicy p sat
