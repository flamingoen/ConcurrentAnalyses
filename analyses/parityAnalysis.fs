module ParityAnalysis

open Defines
open ConstraintAnalysis
open ProgramGraphs

let parityOf x state = Set.fold (fun rst (y,parity,c) -> if y=x then Set.add parity rst else rst ) Set.empty state

let plus = function
    | Odd,Odd   -> Set.ofList [Even]
    | Odd,Even  -> Set.ofList [Odd]
    | Even,Odd  -> Set.ofList [Odd]
    | Even,Even -> Set.ofList [Even]
    | _         -> Set.ofList [P_Undefined]
let minus  = function
    | Odd,Odd   -> Set.ofList [Even]
    | Odd,Even  -> Set.ofList [Odd]
    | Even,Odd  -> Set.ofList [Odd]
    | Even,Even -> Set.ofList [Even]
    | _         -> Set.ofList [P_Undefined]
let multi = function
    | Even,Even -> Set.ofList [Even]
    | Odd,Even  -> Set.ofList [Even]
    | Even,Odd  -> Set.ofList [Even]
    | Odd,Odd   -> Set.ofList [Odd]
    | _         -> Set.ofList [P_Undefined]
let divide = function
    | Even,Even -> Set.ofList [Even; Odd]
    | Odd,Even  -> Set.ofList [Even; Odd]
    | Even,Odd  -> Set.ofList [Even; Odd]
    | Odd,Odd   -> Set.ofList [Even; Odd]
    | _         -> Set.ofList [P_Undefined]
let modulo = function
    | Even,Even -> Set.ofList [Even]
    | Odd,Even  -> Set.ofList [Even]
    | Even,Odd  -> Set.ofList [Odd]
    | Odd,Odd   -> Set.ofList [Odd]
    | _         -> Set.ofList [P_Undefined]

let rec Ap state = function
    | Node(X(x),_)            -> parityOf x state
    | Node(A(arr),_)          -> parityOf arr state
    | Node(C(ch),_)           -> parityOf ch state
    | Node(N(0),_)            -> Set.ofList [Even]
    | Node(N(n),t) when n<0   -> Ap state (Node(N(-n),t))
    | Node(N(n),_) when n%2=0 -> Set.ofList [Even]
    | Node(N(n),_) when n%2=1 -> Set.ofList [Odd]
    | Node(Pl,a1::a2::_)      -> magic (Ap state a1) (Ap state a2) plus
    | Node(Mi,a1::a2::_)      -> magic (Ap state a1) (Ap state a2) minus
    | Node(Mlt,a1::a2::_)     -> magic (Ap state a1) (Ap state a2) multi
    | Node(Div,a1::a2::_)     -> magic (Ap state a1) (Ap state a2) divide
    | Node(Mod,a1::a2::_)     -> magic (Ap state a1) (Ap state a2) modulo
    | _                       -> failwith("In As: unknown match for action")

let rec Bp state = function
    | _ -> Set.ofList[True]

let top_p G =
    let vars = varsInGraph G
    Set.fold (fun rst var -> (Set.ofList [(var,Even,Ø);(var,Odd,Ø)])+rst ) Ø vars

let Lp G =
    let lob s1 s2 = Set.(+) (s1,s2)
    let dif s1 s2 = Set.difference s1 s2
    (Ø,(top_p G),lob,dif)

let lob_p (s1,c1) (s2,c2) = ((Set.union s1 s2),(Set.intersect c1 c2))
let dif_p (s1,c1) (s2,c2) = ((Set.difference s1 s2),(Set.difference c1 c2))

let Lpc G = ((Ø,(btm_Cp G)),((top_p G),Ø),lob_p,dif_p)

let ruleToParity = function
    | R_Even -> Set.ofList [Even]
    | R_Odd  -> Set.ofList [Odd]
    | _      -> Set.ofList [Even; Odd]

let exVal_p G p =
    let vars = (removeLocalVars (varsInGraph G))+(channelsInGraph G)
    let polic = List.fold (fun xs (Policy(v,r)) ->
        if Set.contains v vars then
            Set.fold (fun xs' sign -> Set.add (v,sign,Ø) xs' ) xs (ruleToParity r)
        else xs ) Ø p
    let exclVars = List.fold (fun xs (Policy(v,r)) -> Set.add v xs ) Ø p
    let ex_p = Set.fold (fun rst var ->
        (Set.ofList [(var,Even,Ø);(var,Odd,Ø)])+rst) polic (vars-exclVars)
    (ex_p,exVal_C)

let con_pg Lc id (Ss,Cs) c =
    let cs = Map.fold (fun r id' s -> if id'=id then r else r+s ) Set.empty c
    //let S = removeOrigin (Set.filter (fun (v,s,o,c) -> o=Global ) s2)
    //let cs' = Set.fold (fun rst (v,s,cstr) ->
    //    if Set.intersect S cstr = cstr then Set.add (v,s,Concurrent,cstr) rst else rst ) Set.empty cs
    (cs,(btm Lc))

let con_pa (Ss,Sc) (qs,a,qt,id) c =
    match Map.tryFind id c with
        | Some(s) -> Map.add id (Set.union s Ss) c
        | None    -> Map.add id Ss c

let update x p c state =
    let rSet = Set.filter (fun (y,p,c') -> not (x=y) ) state
    Set.fold (fun rst parity -> Set.add (x,parity,c) rst
    ) rSet p

let p_p p (s,c) =
    List.forall (fun (Policy(v,r)) ->
        Set.fold (fun xs (v',s,c) -> v=v' && Set.contains s (ruleToParity r) || xs ) false s ) p

let f_p (Lp,Lc) (Sp,Sc) (qs,a,qt,id) =
    let Sc' = f_C Bp Lp Lc Sp Sc (qs,a,qt,id)
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  ->
        ((update x (Ap Sp fu) Sc Sp),Sc')
    | Node( Assign, Node(A(ar),l)::fu::[] ) ->
        ((update ar (Ap Sp fu+(Ap Sp (Node(A(ar),l)))) Sc Sp),Sc')
    | Node( Decl,   Node(X(x),_)::xs )      ->
        ((update x (Set.ofList [Even]) Sc Sp),Sc')
    | Node( Decl,   Node(A(ar),l)::xs)      ->
        ((update ar ((Ap Sp (Node(A(ar),l)))+(Set.ofList [Even])) Sc Sp),Sc')
    | Node( Send,   Node(C(ch),_)::x::xs)   ->
        ((update ch (Ap Sp x) Sc Sp),Sc')
    | Node( Recv,   ch::Node(X(x),_)::xs)   ->
        ((update x (Ap Sp ch) Sc Sp),Sc')
    | Node( Recv,   ch::Node(A(ar),l)::xs)  ->
        ((update ar ( (Ap Sp ch) + (Ap Sp (Node(A(ar),l))) ) Sc Sp),Sc')
    | _ ->
        (Sp,Sc')

let parityToString = function
    | Odd -> "o"
    | Even -> "e"
    | P_Undefined -> "err."
