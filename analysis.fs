module analysis

open lattice
open bitVectorAnalyses
open signAnalysis


// ########################################
// ##### Information prints and stuff #####
// ########################################

let mutable transitions = 0
let mutable maxWSize = 0

let printStep (qs,a,qt) Aa Af W L =
    //let Ws = List.foldBack (fun (qs,a,qt) rst -> (qs,(nodeToString a),qt)::rst ) W List.empty
    //printfn("%A->%A:\t  %-10s W: %A") qs qt (nodeToString a) (List.length W)
    //printMap Aa
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

let appendFront t W = t::W
let appendBack  t W = W@[t]

let rec newW G (qs,a,qt) w append = function
    | [] -> w@[(qs,a,qt)]
    | (qs',a',qt')::xs when qs'=qt ->
        newW G (qs,a,qt) (append (qs',a',qt') w) append xs
    | x::xs -> newW G (qs,a,qt) w append xs ;;

let rec MFP2 L Aa f con F W =
    match W with
    | [] -> Aa
    | (qs,a,qt)::xs ->
        let Aa' = lob (f (Map.find qs Aa) (qs,a,qt)) (con Aa qt L) L
        let analysisChanged = (not (subeq Aa' (Map.find qt Aa) L))
        printStep (qs,a,qt) Aa Aa' xs L
        updateStats xs
        if analysisChanged then
            let updatedAnalysis = (Map.add qt (lob Aa' (Map.find qt Aa) L) Aa)
            let updatedWorkList = newW F (qs,a,qt) xs appendBack F
            MFP2 L updatedAnalysis f con F updatedWorkList
        else MFP2 L Aa f con F xs

let MFP L G E i f con =
    let Q = allNodes G
    let A = initA Q L E i
    MFP2 L A f con G G
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
    let f = f_RD non L
    let con = con_RD graph cmps
    let res_t = MFP L graph E exVal f con
    let res = List.fold (fun rst q -> Map.add q ( (Map.find q rst)+(con_RD graph cmps rst q L) ) rst ) res_t E
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2,s) -> printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes graph)) (List.length graph)

let liveVariables G ex =
    printf"\nLive variables:"
    let graph = inverse G
    let L = (btm_LV, (top_LV graph), order_LV)
    let E = List.fold (fun rst (qs,qt) -> qt::rst ) [] ex
    let exVal = exVal_LV
    let cmps = (components graph (allNodes graph))
    let f = f_LV L
    let con = con_LV graph cmps
    let res_t = MFP L graph E exVal f con
    let res = List.fold (fun rst q -> Map.add q ( (Map.find q rst)+(con_LV graph cmps rst q L) ) rst ) res_t E
    printfn("\n")
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,s) -> printf("%s " ) x) state)
        printfn("")
        ) res
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes graph)) (List.length graph)

let rec condenseState state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o) -> x=var ) state
        let conVarSet = Set.fold (fun rst (x,sign,o) -> Set.add (x,sign) rst ) Set.empty varSet
        Set.add (var,(Set.foldBack (fun (x,s) rst -> if rst="" then s+rst else s+","+rst ) conVarSet  "")) (condenseState extract xs)

let detectionOfSignsAnalysis graph ex =
    printfn"\nDetection of signs:"
    let L = (btm_s, (top_s graph), order_s)
    let E = List.fold (fun rst (qs,qt) -> qs::rst ) [] ex
    let exVal = exVal_s graph
    let cmps = (components graph (allNodes graph))
    let f = f_s
    let con = con_S graph cmps
    let res_t = MFP L graph E exVal f con
    let res = List.fold (fun rst q -> Map.add q ( (Map.find q rst)+(con_S graph cmps rst q L) ) rst ) res_t E
    printfn "\n"
    let colRes = Map.fold (fun rst q state ->
        Map.add q ( condenseState state (Set.toList (varsIn state)) ) rst ) Map.empty res
    Map.iter (fun q state ->
        printf("q%-15A") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s " ) x s) state
        printfn("")
        ) colRes
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes graph)) (List.length graph)
    res

let constraintAnalysis graph ex =
    printfn"\nConstraint analysis"
    let Lc = ((btm_C graph),top_C,order_C)
    let Ls = (btm_s, (top_s graph), order_s)
    let E = List.fold (fun rst (qs,qt) -> qs::rst ) [] ex
    let exVal = exVal_C
    let Ss = (detectionOfSignsAnalysis graph ex)
    let f = f_C Ls Lc Ss
    let con = con_C
    let res = MFP Lc graph E exVal f con
    printMap res
