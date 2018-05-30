module ParityAnalysis

open Defines
open ConstraintAnalysis
open IntegerAnalysis
open ProgramGraphs

let parityOf x state = Set.fold (fun rst (y,parity) -> if y=x then Set.add parity rst else rst ) Set.empty state

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
    Set.fold (fun rst var -> (Set.ofList [(var,Even);(var,Odd)])+rst ) Ø vars

let Lp G =
    let lob s1 s2 = Set.(+) (s1,s2)
    (Ø,(top_p G),lob)

let ruleToParity = function
    | R_Even -> Set.ofList [Even]
    | R_Odd  -> Set.ofList [Odd]
    | _      -> Set.ofList [Even; Odd]

let exVal_p G p =
    let vars = (removeLocalVars (varsInGraph G))+(channelsInGraph G)
    let polic = List.fold (fun xs (Policy(v,r)) ->
        if Set.contains v vars then
            Set.fold (fun xs' sign -> Set.add (v,sign) xs' ) xs (ruleToParity r)
        else xs ) Ø p
    let exclVars = List.fold (fun xs (Policy(v,r)) -> Set.add v xs ) Ø p
    Set.fold (fun rst var -> (Set.ofList [(var,Even);(var,Odd)])+rst) polic (vars-exclVars)

let ConstraintSatisfied cr Ss =
    if Set.isEmpty cr then true
    else Set.fold (fun r' inner -> r' || Set.fold (fun r cnstr -> (Set.contains True (Bp Ss cnstr)) && r) true inner ) false cr

let con_pg id Ss c =
    let t = Map.fold (fun r id' s -> if id'=id then r else r+s ) Ø c
    Set.fold(fun r (s,cr) -> if ConstraintSatisfied cr Ss then Set.add s r else r ) Ø t

let con_pa cr Ss (qs,a,qt,id) c =
    let t = match a with
                | Node( Assign, Node(X(x),_)::fu::[] )  -> Set.fold (fun r par -> Set.add (x,par) r ) Ø (Ap Ss fu)
                | Node( Assign, Node(A(ar),l)::fu::[] ) -> Set.fold (fun r par -> Set.add (ar,par) r ) Ø (Ap Ss fu)
                | Node( Decl,   Node(X(x),_)::xs )      -> Set.ofList [(x,Even)]
                | Node( Decl,   Node(A(ar),l)::xs)      -> Set.ofList [(ar,Odd)]
                | Node( Send,   Node(C(ch),_)::x::xs)   -> Set.fold (fun r par -> Set.add (ch,par) r ) Ø (Ap Ss x)
                | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.fold (fun r par -> Set.add (x,par) r ) Ø (Ap Ss ch)
                | Node( Recv,   ch::Node(A(ar),l)::xs)  -> Set.fold (fun r par -> Set.add (ar,par) r ) Ø (Ap Ss ch)
                | _                                     -> Ø
    let s' = Set.fold(fun r s -> Set.add (s,(Map.find qs cr)) r) Ø t
    match Map.tryFind id c with
        | Some(s) -> Map.add id (Set.union s s') c
        | None    -> Map.add id s' c

let update x p state =
    let rSet = Set.filter (fun (y,p) -> not (x=y) ) state
    Set.fold (fun rst parity -> Set.add (x,parity) rst
    ) rSet p

let p_p p s =
    List.forall (fun (Policy(v,r)) ->
        Set.fold (fun xs (v',s) -> v=v' && Set.contains s (ruleToParity r) || xs ) false s ) p

let f_p Sp (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  -> (update x (Ap Sp fu) Sp)
    | Node( Assign, Node(A(ar),l)::fu::[] ) -> (update ar (Ap Sp fu+(Ap Sp (Node(A(ar),l)))) Sp)
    | Node( Decl,   Node(X(x),_)::xs )      -> (update x (Set.ofList [Even]) Sp)
    | Node( Decl,   Node(A(ar),l)::xs)      -> (update ar ((Ap Sp (Node(A(ar),l)))+(Set.ofList [Even])) Sp)
    | Node( Send,   Node(C(ch),_)::x::xs)   -> (update ch (Ap Sp x) Sp)
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> (update x (Ap Sp ch) Sp)
    | Node( Recv,   ch::Node(A(ar),l)::xs)  -> (update ar ( (Ap Sp ch) + (Ap Sp (Node(A(ar),l))) ) Sp)
    | _ -> Sp

let parityToString = function
    | Odd -> "o"
    | Even -> "e"
    | P_Undefined -> "err."
