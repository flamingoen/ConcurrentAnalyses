module bitVectorAnalyses
open lattice

let BVF kill gen con Aa (qs,a,qt) L =
    let sigma = (Map.find qs Aa)
    let t = (qs,a,qt)
    lob ((Set.difference sigma (kill Aa t L)) + (gen Aa t L)) (con Aa qs L) L

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
    Set.fold (fun rst var -> Set.add (var,non,non,Initial) rst) Set.empty (varsInGraph G)

let con_RD G cmps Aa q L =
    let distachedNodes = QQ q G cmps
    let cc = Set.fold (fun rst q -> rst + (Set.filter (fun (v,q1,q2,c) -> c=Global ) (Map.find q Aa)) ) Set.empty distachedNodes
    Set.fold (fun rst (v,q1,q2,c) -> Set.add (v,q1,q2,Concurrent) rst ) Set.empty cc
    ;;

let kill_RD non Aa (qs,a,qt) L =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      -> Set.filter (fun ( var,q1,q2,s) -> var=x ) (Map.find qs Aa )
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.filter (fun ( var,q1,q2,s) -> var=x ) (Map.find qs Aa )
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.filter (fun ( var,q1,q2,s) -> var=x ) (Map.find qs Aa )
    | _ -> Set.empty
    ;;

let gen_RD non Aa (qs,a,qt) L =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      -> Set.ofList [(x,qs,qt,Global )]
    | Node( Assign, Node(A(arr),_)::xs )    -> Set.ofList [(arr,qs,qt,Global )]
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.ofList [(x,qs,qt,Global )]
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.ofList [(x,qs,qt,Global )]
    | _ -> Set.empty
    ;;

let f_RD non cmps G L Aa t = BVF (kill_RD non) (gen_RD non) (con_RD G cmps) Aa t L
