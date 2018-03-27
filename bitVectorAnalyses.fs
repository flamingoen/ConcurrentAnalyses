module bitVectorAnalyses
open lattice

let BVF kill gen state (qs,a,qt) L =
    let t = (qs,a,qt)
    (Set.difference state (kill state t L)) + (gen state t L)

// #### REACHING DEFINITIONS ####

let combine x s = Set.fold (fun rst y -> Set.add (x,y) rst ) Set.empty s

let top_RD G =
    let nodes = (allNodes G)
    let vars = (varsInGraph G)
    let c = Set.empty
    let nCombo = Set.fold (fun rst q -> rst + (combine q nodes) ) Set.empty nodes
    let vCombo = Set.fold (fun rst var -> rst + (Set.fold (fun rst (q1,q2) -> Set.add (var,q1,q2,Global) rst) Set.empty nCombo) ) Set.empty vars
    vCombo
    ;;

let btm_RD = Set.empty ;;

let order_RD s1 s2 = Set.(+) (s1,s2) ;;

let exVal_RD G non =
    Set.fold (fun rst var -> Set.add (var,non,non,Initial) rst) Set.empty (removeLocalVars (varsInGraph G))

let con_RD G cmps Aa q L =
    let distachedNodes = QQ q G cmps
    let cc = Set.fold (fun rst q -> rst + (Set.filter (fun (v,q1,q2,c) -> c=Global ) (Map.find q Aa)) ) Set.empty distachedNodes
    Set.fold (fun rst (v,q1,q2,c) -> Set.add (v,q1,q2,Concurrent) rst ) Set.empty cc
    ;;

let kill_RD non state (qs,a,qt) L =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      -> Set.filter (fun ( var,q1,q2,o) -> var=x ) state
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.filter (fun ( var,q1,q2,o) -> var=x ) state
    | Node( Decl,   Node(A(arr),_)::xs )    -> Set.filter (fun ( var,q1,q2,o) -> var=arr ) state
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.filter (fun ( var,q1,q2,o) -> var=x ) state
    | _ -> Set.empty
    ;;

let gen_RD non state (qs,a,qt) L =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      ->
        if isLocal x then Set.ofList [(x,qs,qt,Local )]
        else Set.ofList [(x,qs,qt,Global )]
    | Node( Assign, Node(A(arr),_)::xs )    ->
        if isLocal arr then Set.ofList [(arr,qs,qt,Local )]
        else Set.ofList [(arr,qs,qt,Global )]
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.ofList [(x,qs,qt,Local )]
    | Node( Recv,   ch::Node(X(x),_)::xs)   ->
        if isLocal x then Set.ofList [(x,qs,qt,Local)]
        else Set.ofList [(x,qs,qt,Global )]
    | _ -> Set.empty
    ;;

let f_RD non L state t = BVF (kill_RD non) (gen_RD non) state t L



// #### Live variables ####

let btm_LV = Set.empty
let top_LV G = Set.empty
let order_LV s1 s2 = Set.(+) (s1,s2) ;;
let exVal_LV = Set.empty

let rec FV = function
    | Node(A(x),_) when isLocal x  -> Set.ofList [(x,Local)]
    | Node(A(x),_)                 -> Set.ofList [(x,Global)]
    | Node(X(x),_)                 -> Set.ofList [(x,Global)]
    | Node(X(x),_) when isLocal x  -> Set.ofList [(x,Local)]
    | Node(_,lst)                  -> List.fold (fun rst x -> rst + (FV x)) Set.empty lst
    ;;

let con_LV G cmps Aa q L =
    let distachedNodes = QQ q G cmps
    let cc = Set.fold (fun rst q -> rst + (Set.filter (fun (v,o) -> o=Global ) (Map.find q Aa)) ) Set.empty distachedNodes
    Set.fold (fun rst (v,o) -> Set.add (v,Concurrent) rst ) Set.empty cc
    ;;

let kill_LV state (qs,a,qt) L =
    match a with
    | Node( Assign, Node(X(x),_)::xs )   -> Set.filter (fun (var,o) -> var=x ) state
    | Node( Decl,   Node(X(x),_)::xs )   -> Set.filter (fun (var,o) -> var=x ) state
    | Node( Decl,   Node(A(arr),_)::xs ) -> Set.filter (fun (var,o) -> var=arr ) state
    | _                                  -> Set.empty

let gen_LV state (qs,a,qt) L =
    match a with
    | Node( Assign, x::arthm::xs )  -> FV arthm
    | Node( Send,   ch::arthm::xs)  -> FV arthm
    | _ -> Set.empty
    ;;

let f_LV L state t = BVF (kill_LV) (gen_LV) state t L
