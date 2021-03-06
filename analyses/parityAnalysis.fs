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
    | Odd,Even  -> Set.ofList [Even; Odd]
    | Even,Odd  -> Set.ofList [Even; Odd]
    | Odd,Odd   -> Set.ofList [Even; Odd]
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

let Lp G =
    let lob s1 s2 = Set.(+) (s1,s2)
    (Ø,lob)

let ruleToParity = function
    | R_Even                -> Set.ofList [Even]
    | R_Odd                 -> Set.ofList [Odd]
    | _                     -> Set.ofList []

let getPolicyMapI pList =
    List.fold (fun xs (Policy(v,r)) ->
        match Map.tryFind v xs with
        | None      -> Map.add v (ruleToParity r) xs
        | Some(s)   ->  Map.add v ( Set.union s (ruleToParity r) ) xs
    ) Map.empty pList
let getPolicyMap p =
    let setMap = List.fold(fun r pList -> Set.add (getPolicyMapI pList) r) Ø p
    Set.fold(fun r map ->
        Map.fold(fun resMap var set ->
            if Set.isEmpty set then resMap else
                match Map.tryFind var r with
                | None -> Map.add var set resMap
                | Some(s) ->  Map.add var ( Set.intersect s set ) resMap
        ) r map
    ) Map.empty setMap
let exVal_p G p =
    let vars = (removeLocalVars (varsInGraph G))+(channelsInGraph G)
    let policyMap = getPolicyMap p
    let polic = Map.fold (fun xs v s -> if Set.contains v vars then Set.fold (fun xs' sign -> Set.add (v,sign) xs' ) xs s else xs ) Ø policyMap
    let exclVars = List.fold(fun r' pList -> r' + List.fold(fun xs (Policy(v,r)) -> if Set.isEmpty (ruleToParity r) then xs else Set.add v xs ) Ø pList ) Ø p
    Set.fold (fun rst var -> (Set.ofList [(var,Even);(var,Odd)])+rst) polic (vars-exclVars)

let ConstraintSatisfied cr Ss =
    if Set.isEmpty cr then true
    else Set.fold (fun r' inner -> r' || Set.fold (fun r cnstr -> (Set.contains True (Bp Ss cnstr)) && r) true inner ) false cr

let con_pg id Ss c =
    let t = Map.fold (fun r id' s -> if id'=id then r else r+s ) Ø c
    Set.fold(fun r (s,cr) -> if ConstraintSatisfied cr Ss then Set.add s r else r ) Ø t

let con_pa cr Ss (qs,a,qt,id) c =
    let t = match a with
                | Node( Assign, Node(X(x),_)::fu::[] )  when not(isLocal x) ->
                    Set.fold (fun r par -> Set.add (x,par) r ) Ø (Ap Ss fu)
                | Node( Assign, Node(A(ar),l)::fu::[] ) when  not(isLocal ar) ->
                    Set.fold (fun r par -> Set.add (ar,par) r ) Ø (Ap Ss fu)
                | Node( Send,   Node(C(ch),_)::x::xs) ->
                    Set.fold (fun r par -> Set.add (ch,par) r ) Ø (Ap Ss x)
                | Node( Recv,   ch::Node(X(x),_)::xs) when not(isLocal x) ->
                    Set.fold (fun r par -> Set.add (x,par) r ) Ø (Ap Ss ch)
                | Node( Recv,   ch::Node(A(ar),l)::xs) when not(isLocal ar) ->
                    Set.fold (fun r par -> Set.add (ar,par) r ) Ø (Ap Ss ch)
                | _ -> Ø
    let s' = Set.fold(fun r s -> Set.add (s,(Map.find qs cr)) r) Ø t
    match Map.tryFind id c with
        | Some(s) -> Map.add id (Set.union s s') c
        | None    -> Map.add id s' c

let update x p state =
    let rSet = Set.filter (fun (y,p) -> not (x=y) ) state
    Set.fold (fun rst parity -> Set.add (x,parity) rst
    ) rSet p

let ruleSatisfied_P state (Policy(var,r)) =
    let SetOfVar = Set.fold(fun r (v,s) -> if var=v then Set.add s r else r) Ø state
    let rule = (ruleToParity r)
    if Set.isEmpty rule then Unknown
    else if Set.isSubset SetOfVar rule then Satisfied
    else if Set.isSuperset SetOfVar rule then Unknown
    else Unsatisfied

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

let framework_p cr G p =
    let l = Lp G
    let ex = exVal_p G p
    (f_p,l,ex,con_pa cr,con_pg,(policySats ruleSatisfied_P))
