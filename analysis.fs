module analysis

open lattice
open bitVectorAnalyses

let mutable transitions = 0
let mutable maxWSize = 0

let printStep (qs,a,qt) Af W =
    printfn("%A->%A:\t  %-10s W size: %A ") qs qt (nodeToString a) (List.length W)

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

let rec newW G (qs,a,qt) w = function
    | [] -> w
    | (qs',a,qt')::xs when qs'=qt -> newW G (qs,a,qt) ((qs',a,qt')::w) xs
    | (qs',a,qt')::xs when (Set.contains qs' (QQ qs G)) -> newW G (qs,a,qt) ((qs',a,qt')::w) xs
    | x::xs -> newW G (qs,a,qt) w xs ;;

let rec newW_C G (qs,a,qt) w = function
    | [] -> w
    | (qs',a,qt')::xs when qs'=qt -> newW G (qs,a,qt) (w@[(qs',a,qt')]) xs
    | (qs',a,qt')::xs when (Set.contains qs' (QQ qs G)) -> newW G (qs,a,qt) (w@[(qs',a,qt')]) xs
    | x::xs -> newW G (qs,a,qt) w xs ;;

let rec MFP2 L Aa f F W =
    if (List.isEmpty W) then Aa
    else doAnalyses L Aa f F W
and doAnalyses L Aa f F W =
    let (qs,a,qt)::xs = W
    let Af = f Aa (qs,a,qt)
    let analysisChanged = (not (subeq Af (Map.find qt Aa) L))
    printStep (qs,a,qt) Af W
    updateStats W
    if analysisChanged then MFP2 L (Map.add qt (Af+(Map.find qt Aa)) Aa) f F (newW F (qs,a,qt) xs F)
    else MFP2 L Aa f F xs
    ;;

let MFP L F E i f =
    let nodes = allNodes F
    let A = initA nodes L E i
    MFP2 L A f F F
    ;;

let rec varsInA = function
    | Node(X(x),_) -> Set.ofList [x]
    | Node(_,lst) -> List.fold (fun rst a -> rst + (varsInA a)) Set.empty lst
    ;;




// ####################################
// ##### Analysis printing things #####
// ####################################

let reachingDefinition graph ex non =
    printfn"Reaching definition:"
    let L = (btm_RD, (top_RD graph), order_RD)
    let E = List.fold (fun rst (qs,qt) -> qs::rst ) [] ex
    let exVal = (exVal_RD graph non)
    let f = f_RD non graph L
    let res = MFP L graph E exVal f
    printfn ""
    printfn("Transitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes graph)) (List.length graph)
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2,s) -> printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
