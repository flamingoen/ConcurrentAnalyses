module analysis

open lattice
open bitVectorAnalyses

let mutable transitions = 0
let mutable maxWSize = 0

let printStep (qs,a,qt) Af W =
    //printfn("%A->%A:\t  %-10s W size: %A ") qs qt (nodeToString a) (List.length W)
    if transitions%100=0 then printf("\n")
    printf("#")

let updateStats W =
    transitions <- transitions+1
    let len = (List.length W)
    if len > maxWSize then maxWSize <- len




// ##############################
// ##### WORKLIST ALGORITHM #####
// ##############################

let initA nodes L E i =
    let emptyA = Set.fold (fun rst q -> Map.add q (btm L) rst ) Map.empty nodes
    List.fold (fun rst q -> Map.add q i rst ) emptyA E
    ;;

let appendFront t W = W@[t]
let appendBack  t W = t::W

let rec newW G (qs,a,qt) w cmps append = function
    | [] -> w
    | (qs',a,qt')::xs when qs'=qt ->
        newW G (qs,a,qt) (append (qs',a,qt') w) cmps append xs
    | (qs',a,qt')::xs when (Set.contains qs' (QQ qs G cmps)) ->
        newW G (qs,a,qt) (append (qs',a,qt') w) cmps append xs
    | x::xs -> newW G (qs,a,qt) w cmps append xs ;;

let rec MFP2 L Aa f F W cmps =
    match W with
    | [] -> Aa
    | (qs,a,qt)::xs ->
        let Af = f Aa (qs,a,qt)
        let analysisChanged = (not (subeq Af (Map.find qt Aa) L))
        printStep (qs,a,qt) Af W
        updateStats W
        if analysisChanged then
            let updatedAnalysis = (Map.add qt (Af+(Map.find qt Aa)) Aa)
            let updatedWorkList = newW F (qs,a,qt) xs cmps appendBack F
            MFP2 L updatedAnalysis f F updatedWorkList cmps
        else MFP2 L Aa f F xs cmps

let MFP L F E i cmps f =
    let Q = foldSetList cmps
    let A = initA Q L E i
    MFP2 L A f F F cmps
    ;;

let rec varsInA = function
    | Node(X(x),_) -> Set.ofList [x]
    | Node(_,lst) -> List.fold (fun rst a -> rst + (varsInA a)) Set.empty lst
    ;;




// ####################################
// ##### Analysis printing things #####
// ####################################

let reachingDefinition graph ex non =
    printf"\nReaching definition:"
    let L = (btm_RD, (top_RD graph), order_RD)
    let E = List.fold (fun rst (qs,qt) -> qs::rst ) [] ex
    let exVal = (exVal_RD graph non)
    let cmps = (components graph (allNodes graph))
    let f = f_RD non cmps graph L
    let res = MFP L graph E exVal cmps f
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2,s) -> printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes graph)) (List.length graph)
