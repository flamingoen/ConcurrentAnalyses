module programGraphs
open GC

// ##### GRAPH GENERATOR #####

let mutable state = 1 ;;
let newstate() =
    state <- state+1
    state ;;

let doneCg = function
    | Node(guard,g::c::[]) -> Node(Not,[g])
    | _                    -> failwith "Invalid node in done"
    ;;

let pGet p var =
    match Map.tryFind var p with
    | Some(x)   ->
        x
    | None      ->
        var
    ;;

let rec pUpdate p = function
    | Node(X(x),lst)    -> Node(X(pGet p x),lst)
    | Node(A(arr),lst)  -> Node(A(pGet p arr),lst)
    //| Node(a,a1::a2::[]) when (op.ContainsKey a) -> Node(a,[(pUpdate p a1);(pUpdate p a1)])
    //| Node(Decl,[x])    -> Node(Decl,[(pUpdate p x)])
    | Node(action,lst)  -> Node(action,(List.foldBack (fun i rst -> (pUpdate p i)::rst) lst []))
    ;;

let rec Pg qs qt p id tree =
    match tree with
    | Node(Decl,Node(X(x),_)::_) ->
        let p' = Map.add x (x+"{"+(string id)+"}") p
        ([(qs,(pUpdate p' tree),qt)],[],p')
    | Node(Decl,Node(A(arr),_)::_) ->
        let p' = Map.add arr (arr+"{"+(string id)+"}") p
        ([(qs,(pUpdate p' tree),qt)],[],p')
    | Node(Assign,_)    ->
        ([(qs,(pUpdate p tree),qt)],[],p)
    | Node(Send,_)      ->
        ([(qs,(pUpdate p tree),qt)],[],p)
    | Node(Recv,_)      ->
        ([(qs,(pUpdate p tree),qt)],[],p)
    | Node(Skip,_)      ->
        ([(qs,(pUpdate p tree),qt)],[],p)
    | Node(P,t::[])     ->
        Pg qs qt p id t
    | Node(Cp,c1::c2::[]) ->
        let q1 = newstate()
        let q2 = newstate()
        let (lst1,ie1,p1) = (Pg qs qt p (id+1) c1)
        let (lst2,ie2,p2) = (Pg q1 q2 p (id+2) c2)
        ( (List.append lst1 lst2), (q1,q2)::(List.append ie1 ie2), p )
    | Node(If,cg::[])   ->
        Pg qs qt p id cg
    | Node(Do,gc::[])   ->
        let (lst,ie,p') = (Pg qs qs p id gc)
        ((qs,(pUpdate p (doneCg gc)),qt)::lst,ie,Map.empty)
    | Node(Loop,[cg]) ->
        Pg qs qs p id cg
    | Node(Guard,g::c::[])  ->
        let q = newstate()
        let (lst,ie,p') = (Pg q qt p id c)
        ((qs,(pUpdate p' g),q)::lst,ie,p')
    | Node(Gc,gc1::gc2::[]) ->
        let (lst1,ie1,p1) = (Pg qs qt p id gc1)
        let (lst2,ie2,p2) = (Pg qs qt p id gc2)
        ( (List.append lst1 lst2), (List.append ie1 ie2), p)
    | Node(Seq,t1::t2::[])  ->
        let q = newstate()
        let (lst1,ie1,p1) = (Pg qs q p id t1)
        let (lst2,ie2,p2) = (Pg q qt p1 id t2)
        ( (List.append lst1 lst2), (List.append ie1 ie2), p2)
    | Node(action,_) -> failwith ("in PG: unknown action "+(string action))
    ;;

let pgGen tree =
    let (graph,ex,p) = Pg 0 1 Map.empty 0 tree
    (graph,(0,1)::ex)
    ;;

// ##### AUX FUNCTIONS FOR GRAPHS #####

let rec varsInA = function
    | Node(X(x),_) -> Set.ofList [x]
    | Node(_,lst) -> List.fold (fun rst a -> rst + (varsInA a)) Set.empty lst
    ;;

let varsInGraph graph = List.fold (fun rst (qs,a,qt) -> rst + (varsInA a)) Set.empty graph ;;

let edgesFrom q graph = Set.filter (fun (qs,a,qt) -> qs=q ) graph ;;
let edgesTo q graph = Set.filter (fun (qs,a,qt) -> qt=q) graph ;;

let endNodes graph = Set.fold (fun rst (qs,a,qt) -> Set.add qt rst) Set.empty graph ;;
let startNodes graph = Set.fold (fun rst (qs,a,qt) -> Set.add qs rst) Set.empty graph

let rec allNodes graph = List.fold (fun rst (qs,a,qt) -> Set.add qt (Set.add qs rst) ) Set.empty graph ;;

let isLocal var = String.exists (fun c -> c='}') var

let removeLocalVars vars =
    Set.fold (fun rst var ->
        if isLocal var then rst else (Set.add var rst)
    ) Set.empty vars

let rec graphFrom q graph =
    let newEdges = (edgesFrom q graph)
    let newGraph = Set.difference graph newEdges
    let newNodes = endNodes newEdges
    match (Set.isEmpty newEdges) with
        | true -> Set.empty
        | false -> (Set.fold (fun rst q' -> rst + (graphFrom q' newGraph) ) Set.empty newNodes)+newEdges

let rec connectedComponent_I qList colored graph =
    match qList with
    | [] -> colored
    | q::qRst ->
        let newEdges = (edgesFrom q graph) + (edgesTo q graph)
        let newGraph = graph-newEdges
        let newNodes = ((endNodes newEdges) + (startNodes newEdges)) - colored
        connectedComponent_I (qRst@(Set.toList newNodes)) (Set.add q colored) newGraph

let connectedComponent q graph =
    let setGraph = Set.ofList graph
    let qList = [q]
    connectedComponent_I qList Set.empty setGraph

let rec QQ q G = function
    | [] -> Set.empty
    | set::xs when (Set.contains q set) -> (QQ q G xs)
    | set::xs -> set + (QQ q G xs)

let rec components G Q =
    match Set.toList Q with
    | [] -> []
    | q::qrst ->
        let comp = connectedComponent q G
        let newQ = Q-comp
        comp::(components G newQ)

let inverse G = List.foldBack (fun (qs,a,qt) rst -> (qt,a,qs)::rst ) G []

// ##### PRODUCT GRAPH GENERATOR #####

let addToNodes nodes (qs,a,qt) = Set.fold (fun rst q -> Set.add (qs+q,a,qt+q) rst) Set.empty nodes

let merge nodes graph = List.fold (fun rst (qs,a,qt) -> rst + (addToNodes nodes (qs,a,qt)) ) Set.empty graph

let product x y =
    let xNodes = allNodes x
    let yNodes = allNodes y
    let xMerge = (merge yNodes x)
    let yMerge = (merge xNodes y)
    Set.toList (xMerge + yMerge)

let rec productFromList = function
    | x::y::rst -> productFromList ((product x y)::rst)
    | lst::[]   -> lst
    | []        -> []
    ;;

let productGraph graph exVal =
    let setExVal = List.fold (fun rst (qs:int,qt) -> ((Set.ofList [qs]),(Set.ofList [qt]))::rst) [] exVal
    let setisfyNodesGraph = List.fold (fun rst (qs,a,qt) -> ((Set.ofList [qs]),a,(Set.ofList [qt]))::rst) [] graph
    let graphList = List.fold (fun rst (qs,qt) -> (Set.toList (graphFrom qs (Set.ofList setisfyNodesGraph)))::rst) [] setExVal
    let pg = productFromList graphList
    let initVal = List.fold (fun rst ((qs:int),qt) -> Set.add qs rst ) Set.empty exVal
    let endVal = List.fold (fun rst (qs,(qt:int)) -> Set.add qt rst) Set.empty exVal
    (pg,[(initVal,endVal)])
