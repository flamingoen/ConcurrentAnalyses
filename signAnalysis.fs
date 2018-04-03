module signAnalysis
open tablesSign
open lattice

let btm_s = Set.empty ;;

let top_s G =
    let vars = varsInGraph G
    Set.fold (fun rst var ->
        if isLocal var then (Set.ofList [(var,"0",Local);(var,"+",Local);(var,"-",Local)])+rst
        else (Set.ofList [(var,"0",Global);(var,"+",Global);(var,"-",Global)])+rst
    ) Set.empty vars

let order_s s1 s2 = Set.(+) (s1,s2)

let exVal_s G =
    let vars = removeLocalVars (varsInGraph G)
    Set.fold (fun rst var -> (Set.ofList [])+rst) Set.empty vars

let con_Sg id c = Map.fold (fun rst id' s -> if id'=id then rst else rst+s ) Set.empty c

let con_Sa id s1 s2 c =
    let filtered = Set.filter (fun (v,s,o) -> o=Global ) (Set.union s1 s2)
    let s' =  Set.fold (fun rst (v,s,o) -> Set.add (v,s,Concurrent) rst ) Set.empty filtered
    match Map.tryFind id c with
    | Some(s) -> Map.add id (s'+s) c
    | None    -> Map.add id s' c

let signOf x state = Set.fold (fun rst (y,sign,o) -> if y=x then Set.add sign rst else rst ) Set.empty state

let magic s1 s2 op = Set.fold (fun rst e1 -> Set.fold (fun rst e2 -> rst+(op (e1,e2))) Set.empty s2) Set.empty s1

let isBoolOp b = List.contains b [Gt;Lt;Eq;Geq;Leq;Neq;Not;Land;Lor;True;False]

let rec As state = function
    | Node(X(x),_)          -> signOf x state
    | Node(A(arr),_)        -> signOf arr state
    | Node(C(ch),_)         -> signOf ch state
    | Node(N(0),_)          -> Set.ofList ["0"]
    | Node(N(n),_) when n>0 -> Set.ofList ["+"]
    | Node(N(n),_) when n<0 -> Set.ofList ["-"]
    | Node(Pl,a1::a2::_)    -> magic (As state a1) (As state a2) plus
    | Node(Mi,a1::a2::_)    -> magic (As state a1) (As state a2) minus
    | Node(Mlt,a1::a2::_)   -> magic (As state a1) (As state a2) multi
    | Node(Div,a1::a2::_)   -> magic (As state a1) (As state a2) divide
    | Node(a,_)             -> failwith("In As: unknown match for action "+(string a))

let rec Bs state = function
    | Node(True,_)          -> Set.ofList [True]
    | Node(False,_)         -> Set.ofList [False]
    | Node(Gt,a1::a2::_)    -> magic (As state a1) (As state a2) greater
    | Node(Lt,a1::a2::_)    -> magic (As state a1) (As state a2) less
    | Node(Eq,a1::a2::_)    -> magic (As state a1) (As state a2) equal
    | Node(Geq,a1::a2::_)   -> magic (As state a1) (As state a2) greaterEq
    | Node(Leq,a1::a2::_)   -> magic (As state a1) (As state a2) lessEq
    | Node(Neq,a1::a2::_)   -> magic (As state a1) (As state a2) notEqual
    | Node(Not,b1::_)       -> Set.fold (fun rst b -> _not b ) Set.empty (Bs state b1)
    | Node(Lor,b1::b2::_)   -> magic (Bs state b1) (Bs state b2) _or
    | Node(Land,b1::b2::_)  -> magic (Bs state b1) (Bs state b2) _and
    | Node(a,_)             -> failwith("In Bs: unknown match for action "+(string a))

let rec basic state = function
    | []        -> [Set.empty]
    | var::xs   ->
        let varSet,extract = Set.partition (fun (x,signs,o) -> x=var ) state
        Set.fold (fun rst elem ->
            List.fold (fun rst' subset -> (Set.add elem subset)::rst' ) [] (basic extract xs)@rst
        ) [] varSet

let varsIn state = Set.fold (fun rst (x,sign,o) -> Set.add x rst ) Set.empty state

let boolFilter b state =
    let basicList = basic state (Set.toList (varsIn state))
    List.fold (fun rst state' ->
        if (Set.contains True (Bs state' b)) then state' + rst
        else rst
    ) Set.empty basicList

let update x signs state =
    let rSet = Set.filter (fun (y,s,o) -> not (x=y) ) state
    Set.fold (fun rst sign ->
        if isLocal x then Set.add (x,sign,Local) rst
        else Set.add (x,sign,Global) rst
    ) rSet signs

let f_s state (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  ->
        (update x (As state fu) state)
    | Node( Assign, Node(A(ar),l)::fu::[] ) ->
        (update ar (As state fu+(As state (Node(A(ar),l)))) state)
    | Node( Decl,   Node(X(x),_)::xs )      ->
        (update x (Set.ofList ["0"]) state)
    | Node( Decl,   Node(A(ar),l)::xs)      ->
        (update ar ((As state (Node(A(ar),l)))+(Set.ofList ["0"])) state)
    | Node( Send,   Node(C(ch),_)::x::xs)   ->
        (update ch (As state x) state)
    | Node( Recv,   ch::Node(X(x),_)::xs)   ->
        (update x (As state ch) state)
    | Node( Recv,   ch::Node(A(ar),l)::xs)  ->
        (update ar ( (As state ch) + (As state (Node(A(ar),l))) ) state)
    | Node( b, _ ) when isBoolOp b          ->
        (boolFilter a state)
    | _ -> state


// ###############################
// ##### Constraint analysis #####
// ###############################

let removeOrigin set = Set.fold (fun rst (v,s,o) -> Set.add (v,s) rst ) Set.empty set

let removeConcurrent set = removeOrigin (Set.filter (fun (v,s,o) -> (not (o=Concurrent)) ) set)

let btm_C G =
    Set.fold (fun rst var -> (Set.ofList [(var,"0");(var,"+");(var,"-");(var,"T")]) + rst ) Set.empty (varsInGraph G)
let top_C = Set.empty
let order_C s1 s2 = Set.intersect s1 s2
let exVal_C = Set.empty

let con_Cg id c = Set.empty
let con_Ca id s1 s2 c = Set.empty

let f_C Ls Lc Ss Sc (qs,a,qt,id) =
    match a with
    | Node( b, _ ) when isBoolOp b ->
        let vars = varsInA a
        let filtered = Set.filter (fun (x,s) -> (Set.contains x vars)) (removeOrigin (boolFilter a (top Ls) ) )
        (filtered - (removeConcurrent Ss)) + Sc
    | _ -> Sc


// ########################
// ##### Combination  #####
// ########################

let exVal_CS G            = ((exVal_s G),exVal_C)
let btm_CS G              = (btm_s,(btm_C G))
let top_CS G              = ((top_s G),top_C)
let order_CS (s1,c1) (s2,c2) = ((order_s s1 s2),(order_C c1 c2))

//let con_CS G cmps Aa q L  =
//    let (_,c) = Map.find q Aa
//    let s = Map.fold (fun rst q (a,b) -> Map.add q a rst) Map.empty Aa
//    ((con_S G cmps s q L),c)

let f_CS Ls Lc (Ss,Sc) t =
    let Sc' = f_C Ls Lc Ss Sc t
    let Ss' = f_s Ss t
    (Ss',Sc')


// doorstop
