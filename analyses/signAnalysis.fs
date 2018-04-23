module SignAnalysis

open Defines
open Policies
open TablesSign
open ConstraintAnalysis
open ProgramGraphs

let signOf x state = Set.fold (fun rst (y,sign,o,c) -> if y=x then Set.add sign rst else rst ) Set.empty state

let rec Ac state = function
    | Node(X(x),_)          -> signOf x state
    | Node(A(arr),_)        -> signOf arr state
    | Node(C(ch),_)         -> signOf ch state
    | Node(N(0),_)          -> Set.ofList ["0"]
    | Node(N(n),_) when n>0 -> Set.ofList ["+"]
    | Node(N(n),_) when n<0 -> Set.ofList ["-"]
    | Node(Pl,a1::a2::_)    -> magic (Ac state a1) (Ac state a2) plus
    | Node(Mi,a1::a2::_)    -> magic (Ac state a1) (Ac state a2) minus
    | Node(Mlt,a1::a2::_)   -> magic (Ac state a1) (Ac state a2) multi
    | Node(Div,a1::a2::_)   -> magic (Ac state a1) (Ac state a2) divide
    | Node(Mod,a1::a2::_)   -> magic (Ac state a1) (Ac state a2) modulo
    | Node(a,_)             -> failwith("In As: unknown match for action "+(string a))

let rec Bs state = function
    | Node(True,_)          -> Set.ofList [True]
    | Node(False,_)         -> Set.ofList [False]
    | Node(Gt,a1::a2::_)    -> magic (Ac state a1) (Ac state a2) greater
    | Node(Lt,a1::a2::_)    -> magic (Ac state a1) (Ac state a2) less
    | Node(Eq,a1::a2::_)    -> magic (Ac state a1) (Ac state a2) equal
    | Node(Geq,a1::a2::_)   -> magic (Ac state a1) (Ac state a2) greaterEq
    | Node(Leq,a1::a2::_)   -> magic (Ac state a1) (Ac state a2) lessEq
    | Node(Neq,a1::a2::_)   -> magic (Ac state a1) (Ac state a2) notEqual
    | Node(Not,b1::_)       -> Set.fold (fun rst b -> (_not b)+rst ) Set.empty (Bs state b1)
    | Node(Lor,b1::b2::_)   -> magic (Bs state b1) (Bs state b2) _or
    | Node(Land,b1::b2::_)  -> magic (Bs state b1) (Bs state b2) _and
    | Node(a,_)             -> failwith("In Bs: unknown match for action "+(string a))

let top_s G =
    let vars = varsInGraph G
    Set.fold (fun rst var -> if isLocal var then (Set.ofList [(var,"0",Local,Ø);(var,"+",Local,Ø);(var,"-",Local,Ø)])+rst else (Set.ofList [(var,"0",Global,Ø);(var,"+",Global,Ø);(var,"-",Global,Ø)])+rst ) Ø vars

let Ls G =
    let order s1 s2 = Set.(+) (s1,s2)
    (Ø,(top_s G),order)

let order_CS (s1,c1) (s2,c2) = ((Set.union s1 s2),(Set.intersect c1 c2))
let Lcs G = ((Ø,(btm_C G)),((top_s G),Ø),order_CS)

let exVal_CS G =
    let vars = removeLocalVars (varsInGraph G)
    let ex_s = Set.fold (fun rst var ->
        (Set.ofList [(var,"0",Initial,Ø);(var,"+",Initial,Ø);(var,"-",Initial,Ø)])+rst) Ø vars
    (ex_s,exVal_C)

let con_CSg Lc id (s1,c1) (s2,c2) c =
    let cs = Map.fold (fun r id' s -> if id'=id then r else r+s ) Set.empty c
    let S = removeOrigin (Set.filter (fun (v,s,o,c) -> o=Global ) s2)
    let cs' = Set.fold (fun rst (v,s,cstr) ->
        if Set.intersect S cstr = cstr then Set.add (v,s,Concurrent,cstr) rst else rst ) Set.empty cs
    (cs',(btm Lc))

let con_CSa id (s1,c1) (s2,c2) c =
    let s' =  Set.fold (fun rst (v,s,o,c') -> if o = Global then Set.add (v,s,c') rst else rst ) Set.empty (Set.union s1 s2)
    match Map.tryFind id c with
        | Some(s) -> Map.add id (s'+s) c
        | None    -> Map.add id s' c

let update x signs c state =
    let rSet = Set.filter (fun (y,s,o,c') -> not (x=y) ) state
    Set.fold (fun rst sign ->
        if isLocal x then Set.add (x,sign,Local,c) rst
        else Set.add (x,sign,Global,c) rst
    ) rSet signs

let ruleToSign = function
    | R_Pl -> "+"
    | R_Mi -> "-"
    | R_Zr -> "0"

let p_s p (s,c) =
    List.forall (fun (v,r) ->
        Set.fold (fun xs (v',s,o,c) -> ( v=v' && (ruleToSign r)=s) || xs ) false s ) p

let f_CS (Ls,Lc) (Ss,Sc) (qs,a,qt,id) =
    let Sc' = f_C Bs Ls Lc Ss Sc (qs,a,qt,id)
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  ->
        ((update x (Ac Ss fu) Sc Ss),Sc')
    | Node( Assign, Node(A(ar),l)::fu::[] ) ->
        ((update ar (Ac Ss fu+(Ac Ss (Node(A(ar),l)))) Sc Ss),Sc')
    | Node( Decl,   Node(X(x),_)::xs )      ->
        ((update x (Set.ofList ["0"]) Sc Ss),Sc')
    | Node( Decl,   Node(A(ar),l)::xs)      ->
        ((update ar ((Ac Ss (Node(A(ar),l)))+(Set.ofList ["0"])) Sc Ss),Sc')
    | Node( Send,   Node(C(ch),_)::x::xs)   ->
        ((update ch (Ac Ss x) Sc Ss),Sc')
    | Node( Recv,   ch::Node(X(x),_)::xs)   ->
        ((update x (Ac Ss ch) Sc Ss),Sc')
    | Node( Recv,   ch::Node(A(ar),l)::xs)  ->
        ((update ar ( (Ac Ss ch) + (Ac Ss (Node(A(ar),l))) ) Sc Ss),Sc')
    | Node( b, _ ) when isBoolOp b          ->
        ((boolFilter Bs a Ss),Sc')
    | _ -> (Ss,Sc')