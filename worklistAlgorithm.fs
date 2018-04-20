module WorklistAlgorithm

open Lattice
open ProgramGraphs
open GraphViz

// ########################################
// ##### Information prints and stuff #####
// ########################################

let mutable transitions = 0
let mutable maxWSize = 0

let printStep (qs,a,qt,id) W =
    //printfn("id:%A  %A->%A:\t  %-10s W: %A ") id qs qt (nodeToString a) (List.length W)
    //List.iter (fun (qs,a,qt,id) ->  printf"(%A->%A)" qs qt ) W
    //printMap c
    //printfn ""
    if transitions%100=0 then printf("\n")
    printf("#")

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

let rec MFP2 cons Aa c W =
    let (L,E,f,con_g,con_a,G,insert,extract) = cons
    match extract W with
    | None ->
        List.fold (fun rst (q,id) -> Map.add q ( lob (Map.find q rst) (con_g id (btm L) (btm L) c) L ) rst ) Aa E
    | Some((qs,a,qt,id),xs) ->
        printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let newA = f sqs (qs,a,qt,id)
        let s' = lob (newA) (con_g id sqs newA c) L
        let analysisChanged = (not (subeq s' sqt L))
        updateStats xs
        if analysisChanged then
            let Aa' = (Map.add qt (lob s' sqt L) Aa)
            let W' = newW G (qs,a,qt,id) xs insert G
            let c' = con_a id sqs newA c
            MFP2 cons Aa' c' W'
        else MFP2 cons Aa c xs

let MFP L G E i f con_g con_a =
    let Q = allNodes G
    let A = initA Q L E i
    let W = workList_list G
    let cons = (L,E,f,con_g,con_a,G,appendBack_list,extract_list)
    MFP2 (L,E,f,con_g,con_a,G,appendBack_list,extract_list) A Map.empty W
    ;;
