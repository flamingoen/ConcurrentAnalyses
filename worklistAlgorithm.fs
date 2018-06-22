module WorklistAlgorithm

open Defines
open ProgramGraphs
open GraphViz

// ########################################
// ##### Information prints and stuff #####
// ########################################

let mutable transitions = 0
let mutable maxWSize = 0


let updateStats (l,s) =
    transitions <- transitions+1
    let len = ((List.length l) + (Set.count s))
    if len > maxWSize then maxWSize <- len

let printStep (qs,a,qt,id) W=
    printfn("\nid:%A  %A->%A:\t  %-10s") id qs qt (nodeToString a)
    //List.iter (fun (qs,a,qt,id) ->  printf"(%A->%A)" qs qt ) W
    //if (transitions+1)%99=0 then printf("#\n") else printf("#")

// ##############################
// #####   WORKLIST Types   #####
// ##############################

// LIST
let appendFront_list t W = t::W
let appendBack_list  t W = W@[t]
let workList_list G = G
let extract_list = function
    | [] -> None
    | x::xs -> Some(x,xs)

// SET
let append_set t W = Set.add t W
let extract_set W =
    match Set.toList W with
    | [] -> None
    | head::tail -> Some(head,(Set.ofList tail))
let workList_Set G = Set.ofList G

// TUPLE
let append_tup t (l,s) = (l,(Set.add t s))
let extract_tup (l,s) =
    match l with
    | []    -> match (Set.toList s) with
                | []    -> None
                | x::xs -> Some(x,(xs,Ø))
    | x::xs -> Some(x,(xs,s))
let worklist_tup G = (G,Ø)

let W_Set G = (append_set,extract_set,workList_Set G)
let W_tup G = (append_tup,extract_tup,worklist_tup G)
let W_Listb G = (appendBack_list,extract_list,workList_list G)
let W_Listf G = (appendFront_list,extract_list,workList_list G)

let worktype G = W_tup G

// ##############################
// ##### WORKLIST ALGORITHM #####
// ##############################

let initA nodes L E i =
    let emptyA = Set.fold (fun rst q ->
        Map.add q (btm L) rst ) Map.empty nodes
    List.fold (fun rst (q,id) -> Map.add q i rst ) emptyA E

let rec newW G (qs,a,qt,id) w append = function
    //| [] -> append (qs,a,qt,id) w
    | [] -> w
    | (qs',a',qt',id')::xs when qs'=qt ->
        newW G (qs,a,qt,id) (append (qs',a',qt',id') w) append xs
    | (qs',a',qt',id')::xs when not(id'=id) ->
        newW G (qs,a,qt,id) (append (qs',a',qt',id') w) append xs
    | x::xs -> newW G (qs,a,qt,id) w append xs

let rec MFP2 cons Aa W =
    let (L,E,f,G,insert,extract) = cons
    match extract W with
    | None -> Aa
    | Some((qs,a,qt,id),xs) ->
        //printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let s' = f sqs (qs,a,qt,id)
        let analysisChanged = (not (subeq s' sqt L))
        if analysisChanged then
            let sqt' = (lob s' sqt L)
            let Aa' = (Map.add qt sqt' Aa)
            let W' = newW G (qs,a,qt,id) xs insert G
            MFP2 cons Aa' W'
        else MFP2 cons Aa xs

let MFP L G E i f =
    let Q = allNodes G
    let A = initA Q L E i
    let (push,pull,W) = worktype G
    let cons = (L,E,f,G,push,pull)
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
        //printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let s' = lob (f sqs (qs,a,qt,id)) (con_g id sqt c) L
        let analysisChanged = (not (subeq s' sqt L))
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
    let (push,pull,W) = worktype G
    let cons = (L,E,f,con_g,con_a,G,push,pull)
    MFPc2 cons A Map.empty W

// #######################################
// ##### WORKLIST ALGORITHM POLICIES #####
// #######################################

let rec MFPp2 cons Aa c W p =
    let (L,E,f,con_g,con_a,G,insert,extract,policySatisfied) = cons
    updateStats W
    match extract W with
    | None ->
        List.fold (fun (ai,pi) (q,id) ->
            let qs' = ( lob (Map.find q ai) (con_g id (btm L) c) L )
            let p'  = Map.add q ( (Map.find q pi) .& pl_concat(policySatisfied qs')) pi
            let Aa' = (Map.add q qs' ai)
            (Aa', p') ) (Aa,p) E
    | Some((qs,a,qt,id),xs) ->
        //printStep (qs,a,qt,id) xs
        let sqs = (Map.find qs Aa)
        let sqt = (Map.find qt Aa)
        let conget = (con_g id sqt c)
        let s' = lob (f sqs (qs,a,qt,id)) conget L
        let analysisChanged = (not (subeq s' sqt L))
        if analysisChanged then
            let sqt' = (lob s' sqt L)
            let Aa' = (Map.add qt sqt' Aa)
            let W' = newW G (qs,a,qt,id) xs insert G
            let c' = con_a sqs (qs,a,qt,id) c
            let p' = Map.add qt ((Map.find qt p) .& (pl_concat (policySatisfied sqt')) ) p
            MFPp2 cons Aa' c' W' p'
        else MFPp2 cons Aa c xs p

let MFPp L G E i f con_g con_a cEmpty ps =
    let Q = allNodes G
    let A = initA Q L E i
    let (push,pull,W) = worktype G
    let cons = (L,E,f,con_g,con_a,G,push,pull,(ps:('a -> (policyList List))))
    let p = Map.fold (fun rst q state ->
        Map.add q (pl_concat (ps state)) rst ) Map.empty A
    MFPp2 cons A cEmpty W p
