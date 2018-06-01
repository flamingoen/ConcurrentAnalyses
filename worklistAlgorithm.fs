module WorklistAlgorithm

open Defines
open ProgramGraphs
open GraphViz

// ########################################
// ##### Information prints and stuff #####
// ########################################

let mutable transitions = 0
let mutable maxWSize = 0

let printStep (qs,a,qt,id) W=
    //printfn("\nid:%A  %A->%A:\t  %-10s W: %A") id qs qt (nodeToString a) (List.length W)
    //List.iter (fun (qs,a,qt,id) ->  printf"(%A->%A)" qs qt ) W
    if (transitions+1)%99=0 then printf("#\n") else printf("#")

let updateStats W =
    transitions <- transitions+1
    let len = (List.length W)
    if len > maxWSize then maxWSize <- len


// ##############################
// #####   WORKLIST Types   #####
// ##############################

let appendFront_list t W = t::W
let appendBack_list  t W = W@[t]
let workList_list G = G
let extract_list = function
    | [] -> None
    | x::xs -> Some(x,xs)

// ##############################
// ##### WORKLIST ALGORITHM #####
// ##############################

let initA nodes L E i =
    let emptyA = Set.fold (fun rst q -> Map.add q (btm L) rst ) Map.empty nodes
    List.fold (fun rst (q,id) -> Map.add q i rst ) emptyA E
    ;;

let rec newW G (qs,a,qt,id) w append = function
    | [] -> append (qs,a,qt,id) w
    | (qs',a',qt',id')::xs when qs'=qt ->
        newW G (qs,a,qt,id) (append (qs',a',qt',id') w) append xs
    //| (qs',a',qt',id')::xs when not(id'=id) ->
    //    newW G (qs,a,qt,id) (append (qs',a',qt',id') w) append xs
    | x::xs -> newW G (qs,a,qt,id) w append xs ;;

let rec MFP2 cons Aa W =
    let (L,E,f,G,insert,extract) = cons
    match extract W with
    | None -> Aa
    | Some((qs,a,qt,id),xs) ->
        printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let s' = f sqs (qs,a,qt,id)
        let analysisChanged = (not (subeq s' sqt L))
        updateStats xs
        if analysisChanged then
            let sqt' = (lob s' sqt L)
            let Aa' = (Map.add qt sqt' Aa)
            let W' = newW G (qs,a,qt,id) xs insert G
            MFP2 cons Aa' W'
        else MFP2 cons Aa xs

let MFP L G E i f =
    let Q = allNodes G
    let A = initA Q L E i
    let W = workList_list G
    let cons = (L,E,f,G,appendBack_list,extract_list)
    MFP2 cons A W


// #########################################
// ##### WORKLIST ALGORITHM CONCURRENT #####
// #########################################

let rec MFPc2 cons Aa c W =
    let (L,E,f,con_g,con_a,G,insert,extract) = cons
    match extract W with
    | None ->
        List.fold (fun rst (q,id) -> Map.add q ( lob (Map.find q rst) (con_g id (btm L) c) L ) rst ) Aa E
    | Some((qs,a,qt,id),xs) ->
        printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let s' = f (lob sqs (con_g id sqs c) L) (qs,a,qt,id)
        let analysisChanged = (not (subeq s' sqt L))
        updateStats xs
        if analysisChanged then
            let sqt' = (lob s' sqt L)
            let Aa' = (Map.add qt sqt' Aa)
            let W' = newW G (qs,a,qt,id) xs insert G
            let c' = con_a sqs (qs,a,qt,id) c
            MFPc2 cons Aa' c' W'
        else MFPc2 cons Aa c xs

let MFPc L G E i f con_g con_a =
    let Q = allNodes G
    let A = initA Q L E i
    let W = workList_list G
    let cons = (L,E,f,con_g,con_a,G,appendBack_list,extract_list)
    MFPc2 cons A Map.empty W

// #######################################
// ##### WORKLIST ALGORITHM POLICIES #####
// #######################################

let rec MFPp2 cons Aa c W =
    let (L,E,f,con_g,con_a,G,insert,extract,policySatisfied) = cons
    match extract W with
    | None ->
        let r = List.fold (fun rst (q,id) -> Map.add q ( lob (Map.find q rst) (con_g id (btm L) c) L ) rst ) Aa E
        let p = Map.fold (fun rst q res -> Map.add q (policySatisfied res) rst ) Map.empty r
        (r,p)
    | Some((qs,a,qt,id),xs) ->
        printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let s' = f (lob sqs (con_g id sqt c) L) (qs,a,qt,id)
        let analysisChanged = (not (subeq s' sqt L))
        updateStats xs
        if analysisChanged then
            let sqt' = (lob s' sqt L)
            let Aa' = (Map.add qt sqt' Aa)
            let W' = newW G (qs,a,qt,id) xs insert G
            let c' = con_a sqs (qs,a,qt,id) c
            MFPp2 cons Aa' c' W'
        else MFPp2 cons Aa c xs

let MFPp L G E i f con_g con_a ps =
    let Q = allNodes G
    let A = initA Q L E i
    let W = workList_list G
    let cons = (L,E,f,con_g,con_a,G,appendBack_list,extract_list,ps)
    MFPp2 cons A Map.empty W
