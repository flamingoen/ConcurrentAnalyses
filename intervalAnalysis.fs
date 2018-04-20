module IntervalAnalysis

open ConstraintAnalysis
open Lattice
open ProgramGraphs
open GC

let MAX = 10
let MIN = 0
type interval =
    I of (int*int) | Undefined | Empty
    static member (+) (e1:interval,e2:interval) =
        match (e1,e2) with
        | (Undefined,_) -> Undefined
        | (_,Undefined) -> Undefined
        | (Empty,i)     -> i
        | (i,Empty)     -> i
        | (I(mx,mn),I(mx',mn')) -> I((max mx mx'),(min mn mn'))


let ob_I = I(MAX,MIN)
let lb_I = Empty

let btm_I G = Set.fold (fun rst var ->
    if isLocal var then Set.add (var,lb_I,Local,Ø) rst else Set.add (var,lb_I,Global,Ø) rst ) Ø (varsInGraph G)
let top_I G = Set.fold (fun rst var ->
    if isLocal var then Set.add (var,ob_I,Local,Ø) rst else Set.add (var,ob_I,Global,Ø) rst ) Ø (varsInGraph G)
let order_I s1 s2 =
     let map = Set.fold (fun rst (var,(i:interval),o,c) -> Map.add (var,o,c) i rst ) Map.empty s1
     let newMap = Set.fold (fun rst (var,i,o,c) ->
         match Map.tryFind (var,o,c) map with
         | None -> (Map.add (var,o,c) i rst)
         | Some(i') -> Map.add (var,o,c) (i+i') rst ) map s2
     Map.fold (fun rst (var,o,c) i -> Set.add (var,i,o,c) rst ) Ø newMap

let order_IC (i1,c1) (i2,c2) = ((order_I i1 i2),(Set.intersect c1 c2))
let L_I G = (((btm_I G),(btm_Ci G ob_I)),((top_I G),Ø),order_IC)

let exVal_I G =
    let vars = removeLocalVars (varsInGraph G)
    let eI = Set.fold (fun rst var -> (Set.ofList [(var,ob_I,Initial,Ø)])+rst) Ø vars
    (eI,exVal_C)

let con_Ig Lc id (s1,c1) (s2,c2) c =
    let cs = Map.fold (fun r id' s -> if id'=id then r else (order_I r s) ) Ø c
    let S = removeOrigin (Set.filter (fun (v,i,o,c) -> o=Global ) s2)
    let cs' = Set.fold (fun rst (v,s,o,c) ->
        let c' = removeOrigin c
        if Set.intersect S c' = c' then Set.add (v,s,o,c) rst else rst ) Ø cs
    (cs',(btm Lc))
let con_Ia id (s1,c1) (s2,c2) c =
    let s' =  Set.fold (fun rst (v,i,o,c') -> if o=Global && not(i=Empty) then Set.add (v,i,Concurrent,c') rst else rst ) Set.empty (order_I s1 s2)
    match Map.tryFind id c with
        | Some(s) -> Map.add id (order_I s' s) c
        | None    -> Map.add id s' c

let plus = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (I(mx,mn),I(mx',mn')) -> I( (min (mx+mx') MAX ),(max (mn+mn') MIN) )
    | (_,_)                 -> Empty
let minus  = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (I(mx,mn),I(mx',mn')) -> I( (min (mx+mn') MAX ),(max (mn+mx') MIN ) )
    | (_,_)                 -> Empty
let multi = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (I(mx,mn),I(mx',mn')) ->
        let first = min (max (max (mx*mn') (mx*mx') ) (max (mn*mx') (mn*mn') )) MAX
        let second = max (min (min (mx*mn') (mx*mx') ) (min (mn*mx') (mn*mn') )) MIN
        I(first,second)
    | (_,_)                 -> Empty
let divide = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (_,I(0,0))            -> Undefined
    | (I(0,0),_)            -> I(0,0)
    | (I(mx,mn),I(mx',mn')) ->
        let first = min (max (max (mx/mn') (mx/mx') ) (max (mn/mx') (mn/mn') )) MAX
        let second = max (min (min (mx/mn') (mx/mx') ) (min (mn/mx') (mn/mn') )) MIN
        I(first,second)
    | (_,_)                 -> Empty
let modulo = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (_,I(0,0))            -> Undefined
    | (I(0,0),_)            -> I(0,0)
    | (I(mx,mn),I(mx',mn')) ->
        let first = min (max (max (mx%mn') (mx%mx') ) (max (mn%mx') (mn%mn') )) MAX
        let second = max (min (min (mx%mn') (mx%mx') ) (min (mn%mx') (mn%mn') )) MIN
        I(first,second)
    | (_,_)                 -> Empty
let greater = function
    | (I(mx,mn),I(mx',mn')) when mn>mx'  -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn')) when mn'>=mx -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn'))              -> Set.ofList [True; False]
    | (_,_)                              -> Ø
let less = function
    | (I(mx,mn),I(mx',mn')) when mx<mn'  -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn')) when mn'<=mx -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn'))              -> Set.ofList [True; False]
    | (_,_)                              -> Ø
let equal = function
    | (I(mx,mn),I(mx',mn')) when mn<mx' -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn')) when mx<mn' -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn')) when mx=mn && mx=mx' && mx=mn' -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn'))             -> Set.ofList [True; False]
    | (_,_)                             -> Ø
let greaterEq = function
    | (I(mx,mn),I(mx',mn')) when mn>=mx' -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn')) when mx>mn'  -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn'))              -> Set.ofList [True; False]
    | (_,_)                              -> Ø
let lessEq = function
    | (I(mx,mn),I(mx',mn')) when mx<=mn' -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn')) when mn'<mx  -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn'))              -> Set.ofList [True; False]
    | (_,_)                              -> Ø
let notEqual = function
    | (I(mx,mn),I(mx',mn')) when mn<mx' -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn')) when mx<mn' -> Set.ofList [True]
    | (I(mx,mn),I(mx',mn')) when mx=mn && mx=mx' && mx=mn' -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn'))              -> Set.ofList [True; False]
    | (_,_)                              -> Ø
let _and = function
    | True,True -> Set.ofList [True]
    | _,_ -> Set.ofList [False]
let _or = function
    | False,False -> Set.ofList [False]
    | _,_ -> Set.ofList [True]
let _not = function
    | True -> Set.ofList [False]
    | _ -> Set.ofList [True]


let intervalOf x state =
    Set.fold (fun rst (v,i,o,c) -> if v=x then rst+i else rst ) Empty state

let rec A_I state = function
    | Node(X(x),_)          -> intervalOf x state
    | Node(A(arr),_)        -> intervalOf arr state
    | Node(C(ch),_)         -> intervalOf ch state
    | Node(N(n),_)          -> I(n,n)
    | Node(Pl,a1::a2::_)    -> plus ((A_I state a1),(A_I state a2))
    | Node(Mi,a1::a2::_)    -> minus ((A_I state a1),(A_I state a2))
    | Node(Mlt,a1::a2::_)   -> multi ((A_I state a1),(A_I state a2))
    | Node(Div,a1::a2::_)   -> divide ((A_I state a1),(A_I state a2))
    | Node(Mod,a1::a2::_)   -> modulo ((A_I state a1),(A_I state a2))
    | Node(a,_)             -> failwith("In As: unknown match for action "+(string a))
let rec B_I state = function
    | Node(True,_)          -> Set.ofList [True]
    | Node(False,_)         -> Set.ofList [False]
    | Node(Gt,a1::a2::_)    -> greater      ((A_I state a1), (A_I state a2))
    | Node(Lt,a1::a2::_)    -> less         ((A_I state a1), (A_I state a2))
    | Node(Eq,a1::a2::_)    -> equal        ((A_I state a1), (A_I state a2))
    | Node(Geq,a1::a2::_)   -> greaterEq    ((A_I state a1), (A_I state a2))
    | Node(Leq,a1::a2::_)   -> lessEq       ((A_I state a1), (A_I state a2))
    | Node(Neq,a1::a2::_)   -> notEqual     ((A_I state a1), (A_I state a2))
    | Node(Not,b1::_)       -> Set.fold (fun rst b -> (_not b)+rst ) Ø (B_I state b1)
    | Node(Lor,b1::b2::_)   -> magic (B_I state b1) (B_I state b2) _or
    | Node(Land,b1::b2::_)  -> magic (B_I state b1) (B_I state b2) _and
    | Node(a,_)             -> failwith("In Bs: unknown match for action "+(string a))

let update x interval c state =
    let rSet = Set.filter (fun (v,i,o,c') -> not (v=x) ) state
    if isLocal x then Set.add (x,interval,Local,c) rSet
    else Set.add (x,interval,Global,c) rSet

let splitIntervalSet s = Set.fold (fun rst (v,i,o,c) ->
    match i with
    | I(max,min) -> (List.fold (fun rst' j -> Set.add (v,I(j,j),o,c) rst' ) Ø [min .. max])+rst
    | _          -> Set.add (v,i,o,c) rst ) Ø s

let mergeIntervalSet s = Set.fold (fun rst e -> order_I (Set.ofList [e]) rst) Ø s

let f_I Li Lc (Ss,Sc) (qs,a,qt,id) =
    let Sc' = f_C B_I Li Lc (splitIntervalSet Ss) Sc (qs,a,qt,id)
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  ->
        (update x (A_I Ss fu) Ø Ss , Sc')
    | Node( Assign, Node(A(ar),l)::fu::[] ) ->
        (update ar ((A_I Ss fu)+(A_I Ss (Node(A(ar),l)))) Ø Ss , Sc')
    | Node( Decl,   Node(X(x),_)::xs )      ->
        (update x (I(0,0)) Ø Ss , Sc')
    | Node( Decl,   Node(A(ar),l)::xs)      ->
        (update ar (I(0,0)) Ø Ss , Sc')
    | Node( Send,   Node(C(ch),_)::x::xs)   ->
        (update ch (A_I Ss x) Ø Ss , Sc')
    | Node( Recv,   ch::Node(X(x),_)::xs)   ->
        (update x (A_I Ss ch) Ø Ss , Sc')
    | Node( Recv,   ch::Node(A(ar),l)::xs)  ->
        (update ar ((A_I Ss ch)+(A_I Ss (Node(A(ar),l)))) Ø Ss , Sc')
    | Node( b, _ ) when isBoolOp b          ->
        let Ss' = mergeIntervalSet (boolFilter B_I a (splitIntervalSet Ss))
        (Ss',Sc')
    | _ ->
        (Ss , Sc')
