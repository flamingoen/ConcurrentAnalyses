module worklistAlgorithm

open lattice

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
