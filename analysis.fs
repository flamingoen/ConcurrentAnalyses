module analysis

open lattice
open bitVectorAnalyses
open signAnalysis


// ########################################
// ##### Information prints and stuff #####
// ########################################

let mutable transitions = 0
let mutable maxWSize = 0

let printStep (qs,a,qt,id) Aa Af W L c=
    //printfn("id:%A  %A->%A:\t  %-10s W: %A") id qs qt (nodeToString a) (List.length W)
    //printMap c
    //printfn ""
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
    List.fold (fun rst (q,id) -> Map.add q i rst ) emptyA E
    ;;

let appendFront t W = t::W
let appendBack  t W = W@[t]

let rec newW G (qs,a,qt,id) w append = function
    | [] -> w@[(qs,a,qt,id)]
    | (qs',a',qt',id')::xs when qs'=qt ->
        newW G (qs,a,qt,id) (append (qs',a',qt',id') w) append xs
    | x::xs -> newW G (qs,a,qt,id) w append xs ;;

let rec MFP2 L E Aa f c con_g con_a F W =
    match W with
    | [] -> List.fold (fun rst (q,id) -> Map.add q ( lob (Map.find q rst) (con_g id (btm L) (btm L) c) L ) rst ) Aa E
    | (qs,a,qt,id)::xs ->
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let newA = f sqs (qs,a,qt,id)
        let s' = lob (newA) (con_g id sqs newA c) L
        let analysisChanged = (not (subeq s' sqt L))
        printStep (qs,a,qt,id) Aa s' xs L c
        updateStats xs
        if analysisChanged then
            let Aa' = (Map.add qt (lob s' sqt L) Aa)
            let W' = newW F (qs,a,qt,id) xs appendBack F
            let c' = con_a id sqs newA c
            MFP2 L E Aa' f c' con_g con_a F W'
        else MFP2 L E Aa f c con_g con_a F xs

let MFP L G E i f con_g con_a =
    let Q = allNodes G
    let A = initA Q L E i
    MFP2 L E A f Map.empty con_g con_a G G
    ;;


// ####################################
// ##### Analysis printing things #####
// ####################################

let reachingDefinition G ex non =
    printf"\nReaching definition:"
    let L = (btm_RD, (top_RD G), order_RD)
    let E = List.fold (fun rst (qs,qt,id) -> (qs,id)::rst ) [] ex
    let exVal = (exVal_RD G non)
    let f = f_RD non
    let res = MFP L G E exVal f con_RDg con_RDa
    printfn "\n"
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,q1,q2,s) -> printf("%s: %A -> %A\t" ) x q1 q2) state)
        printfn("")
        ) res
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes G)) (List.length G)

let liveVariables G ex =
    printf"\nLive variables:"
    let G = inverse G
    let L = (btm_LV, (top_LV G), order_LV)
    let E = List.fold (fun rst (qs,qt,id) -> (qt,id)::rst ) [] ex
    let res = MFP L G E exVal_LV f_LV con_LVg con_LVa
    printfn("\n")
    Map.iter (fun q state ->
        printf("q%A:\t") q
        (Set.iter (fun (x,s) -> printf("%s " ) x) state)
        printfn("")
        ) res
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes G)) (List.length G)

let rec condenseState state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o) -> x=var ) state
        let conVarSet = Set.fold (fun rst (x,sign,o) -> Set.add (x,sign) rst ) Set.empty varSet
        Set.add (var,(Set.foldBack (fun (x,s) rst -> if rst="" then s+rst else s+","+rst ) conVarSet  "")) (condenseState extract xs)

let detectionOfSignsAnalysis G ex =
    printfn"\nDetection of signs:"
    let L = (btm_s, (top_s G), order_s)
    let E = List.fold (fun rst (qs,qt,id) -> (qs,id)::rst ) [] ex
    let exVal = exVal_s G
    let res = MFP L G E exVal f_s con_Sg con_Sa
    printfn "\n"
    let colRes = Map.fold (fun rst q state ->
        Map.add q ( condenseState state (Set.toList (varsIn state)) ) rst ) Map.empty res
    Map.iter (fun q state ->
        printf("q%-15A") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s " ) x s) state
        printfn("")
        ) colRes
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes G)) (List.length G)

let rec condenseStateC state = function
    | []        -> Set.empty
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o,cstr) -> x=var ) state
        let conVarSet = Set.fold (fun rst (x,sign,o,cstr) -> Set.add (x,sign) rst ) Set.empty varSet
        Set.add (var,(Set.foldBack (fun (x,s) rst -> if rst="" then s+rst else s+","+rst ) conVarSet  "")) (condenseStateC extract xs)

let constraintAnalysis graph ex =
    printfn"\nConstraint analysis"
    let L = ((btm_CS graph),(top_CS graph),order_CS)
    let Lc = ((btm_C graph),top_C,order_C)
    let Ls = (btm_s, (top_Sc graph), order_s)
    let E = List.fold (fun rst (qs,qt,id) -> (qs,id)::rst ) [] ex
    let exVal = exVal_CS graph
    let f = f_CS Ls Lc
    let res = MFP L graph E exVal f (con_CSg Lc) con_CSa
    printfn "\n"
    let colRes = Map.fold (fun rst q (s,c) ->
        Map.add q ( condenseStateC s (Set.toList (varsInC s)) , c) rst ) Map.empty res
    Map.iter (fun q (state,c) ->
        printf("q%-10A\t") q
        Set.iter (fun (x,s) -> printf("%5s-> %-5s " ) x s) state
        printf("\t[")
        Set.iter (fun e -> printf("%A") e ) c
        printfn("] ")
        ) colRes
    printfn("\nTransitions taken: %A    Max worklist size: %A    Nodes: %i    Transitions: %i") transitions maxWSize (Set.count (allNodes graph)) (List.length graph)
