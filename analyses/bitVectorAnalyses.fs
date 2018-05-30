module BitVectorAnalyses

open Defines
open ProgramGraphs

let BVF kill gen state t = (Set.difference state (kill state t)) + (gen t)

let con_BVFg id Ss c = Map.fold (fun rst id' s -> if id'=id then rst else rst+s ) Ø c

let combine x s = Set.fold (fun rst y -> Set.add (x,y) rst ) Set.empty s

// #### REACHING DEFINITIONS ####

let top_RD G =
    let nodes = (allNodes G)
    let vars = (varsInGraph G)
    let c = Set.empty
    let nCombo = Set.fold (fun rst q -> rst + (combine q nodes) ) Set.empty nodes
    let vCombo = Set.fold (fun rst var -> rst + (Set.fold (fun rst (q1,q2) -> Set.add (var,q1,q2,Global) rst) Set.empty nCombo) ) Set.empty vars
    vCombo

let lob_RD s1 s2 = Set.(+) (s1,s2)
let L_RD G = (Ø,(top_RD G),lob_RD)

let exVal_RD G non =
    Set.fold (fun rst var -> Set.add (var,non,non) rst) Set.empty (removeLocalVars (varsInGraph G))

let kill_RD state (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      -> Set.filter (fun ( var,q1,q2) -> var=x ) state
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.filter (fun ( var,q1,q2) -> var=x ) state
    | Node( Decl,   Node(A(arr),_)::xs )    -> Set.filter (fun ( var,q1,q2) -> var=arr ) state
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.filter (fun ( var,q1,q2) -> var=x ) state
    | _ -> Set.empty
    ;;

let gen_RD (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      ->
        if isLocal x then Set.ofList [(x,qs,qt)]
        else Set.ofList [(x,qs,qt)]
    | Node( Assign, Node(A(arr),_)::xs )    ->
        if isLocal arr then Set.ofList [(arr,qs,qt)]
        else Set.ofList [(arr,qs,qt)]
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.ofList [(x,qs,qt)]
    | Node( Recv,   ch::Node(X(x),_)::xs)   ->
        if isLocal x then Set.ofList [(x,qs,qt)]
        else Set.ofList [(x,qs,qt)]
    | _ -> Set.empty

let con_RDa (s':Set<_>) (qs,a,qt,id) c =
    let gen = gen_RD (qs,a,qt,id)
    match Map.tryFind id c with
    | Some(s) -> Map.add id (gen+s) c
    | None    -> Map.add id gen c

let f_RD state t = BVF (kill_RD) (gen_RD) state t



// #### Live variables ####

let lob_LV s1 s2 = Set.(+) (s1,s2)
let L_LV = (Ø,Ø,lob_LV)
let exVal_LV = Set.empty

let rec FV = function
    | Node(A(x),_) when isLocal x  -> Set.ofList [x]
    | Node(A(x),_)                 -> Set.ofList [x]
    | Node(X(x),_)                 -> Set.ofList [x]
    | Node(X(x),_) when isLocal x  -> Set.ofList [x]
    | Node(_,lst)                  -> List.fold (fun rst x -> rst + (FV x)) Set.empty lst

let kill_LV state (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::xs )   -> Set.filter (fun (var) -> var=x ) state
    | Node( Decl,   Node(X(x),_)::xs )   -> Set.filter (fun (var) -> var=x ) state
    | Node( Decl,   Node(A(arr),_)::xs ) -> Set.filter (fun (var) -> var=arr ) state
    | _                                  -> Set.empty

let gen_LV (qs,a,qt,id) =
    match a with
    | Node( Assign, x::arthm::xs )  -> FV arthm
    | Node( Send,   ch::arthm::xs)  -> FV arthm
    | _ -> Set.empty

let con_LVa (s':Set<_>) (qs,a,qt,id) c =
    let gen = gen_LV (qs,a,qt,id)
    match Map.tryFind id c with
    | Some(s) -> Map.add id (gen+s) c
    | None    -> Map.add id gen c

let f_LV state t = BVF (kill_LV) (gen_LV) state t
