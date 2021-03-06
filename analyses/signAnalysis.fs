module SignAnalysis

open Defines
open TablesSign
open ConstraintAnalysis
open IntegerAnalysis
open ProgramGraphs

let signOf x state = Set.fold (fun rst (y,sign) -> if y=x then Set.add sign rst else rst ) Set.empty state

let rec Ac state = function
    | Node(X(x),_)          -> signOf x state
    | Node(A(arr),_)        -> signOf arr state
    | Node(C(ch),_)         -> signOf ch state
    | Node(N(0),_)          -> Set.ofList [Zero]
    | Node(N(n),_) when n>0 -> Set.ofList [Pos]
    | Node(N(n),_) when n<0 -> Set.ofList [Neg]
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

let ruleToSign = function
    | R_Pl                  -> Set.ofList [Pos]
    | R_Mi                  -> Set.ofList [Neg]
    | R_Zr                  -> Set.ofList [Zero]
    | R_Grt(n)  when n=0    -> Set.ofList [Pos]
    | R_Grt(n)  when n=(-1) -> Set.ofList [Zero;Pos]
    | R_Lt(n)   when n=0    -> Set.ofList [Neg]
    | R_Lt(n)   when n=1    -> Set.ofList [Zero;Neg]
    | R_Eq(n)   when n=0    -> Set.ofList [Zero]
    | _                     -> Set.ofList []

let Ls G =
    let lob s1 s2 = Set.(+) (s1,s2)
    (Ø,lob)

let getPolicyMapI pList =
    List.fold (fun xs (Policy(v,r)) ->
        match Map.tryFind v xs with
        | None      -> Map.add v (ruleToSign r) xs
        | Some(s)   -> Map.add v ( Set.union s (ruleToSign r) ) xs
    ) Map.empty pList
let getPolicyMap p =
    let setMap = List.fold(fun r pList -> Set.add (getPolicyMapI pList) r) Ø p
    Set.fold(fun r map ->
        Map.fold(fun resMap var set ->
            if Set.isEmpty set then resMap else
                match Map.tryFind var r with
                | None -> Map.add var set resMap
                | Some(s) when Set.isEmpty ( Set.intersect s set ) -> Map.add var ( Set.ofList [S_Undefined]) resMap
                | Some(s) ->  Map.add var ( Set.intersect s set ) resMap ) r map
    ) Map.empty setMap
let exVal_s G p =
    let vars = (removeLocalVars (varsInGraph G))+(channelsInGraph G)
    let policyMap = getPolicyMap (p)
    let polic = Map.fold(fun xs v s ->
        if Set.contains v vars then Set.fold (fun xs' sign -> Set.add (v,sign) xs' ) xs s
        else xs ) Ø policyMap
    let exclVars = List.fold(fun r' pList -> r' + List.fold(fun xs (Policy(v,r)) -> if Set.isEmpty (ruleToSign r) then xs else Set.add v xs ) Ø pList ) Ø (p)
    Set.fold(fun rst var -> (Set.ofList [(var,Zero);(var,Pos);(var,Neg)])+rst ) polic (vars-exclVars)

let con_sa cr Ss (qs,a,qt,id) c =
    let gen = match a with
                | Node( Assign, Node(X(x),_)::fu::[] )  when not(isLocal x) ->
                    Set.fold (fun r sign -> Set.add (x,sign) r ) Ø (Ac Ss fu)
                | Node( Assign, Node(A(ar),l)::fu::[] ) when not(isLocal ar) ->
                    Set.fold (fun r sign -> Set.add (ar,sign) r ) Ø (Ac Ss fu)
                | Node( Send,   Node(C(ch),_)::x::xs)   ->
                    Set.fold (fun r sign -> Set.add (ch,sign) r ) Ø (Ac Ss x)
                | Node( Recv,   ch::Node(X(x),_)::xs)   when not(isLocal x) ->
                    Set.fold (fun r sign -> Set.add (x,sign) r ) Ø (Ac Ss ch)
                | Node( Recv,   ch::Node(A(ar),l)::xs)  when not(isLocal ar) ->
                    Set.fold (fun r sign -> Set.add (ar,sign) r ) Ø (Ac Ss ch)
                | _                                     -> Ø
    let s' = Set.fold(fun r s -> Set.add (s,(Map.find qs cr)) r) Ø gen
    match Map.tryFind id c with
        | Some(s) -> Map.add id (Set.union s s') c
        | None    -> Map.add id s' c

let ConstraintSatisfied cr Ss =
    if Set.isEmpty cr then true
    else Set.fold (fun r' inner -> r' || Set.fold (fun r cnstr -> (Set.contains True (Bs Ss cnstr)) && r) true inner ) false cr
let con_sg cr id Ss c =
    let t = Map.fold (fun r id' s -> if id'=id then r else r+s ) Ø c
    Set.fold(fun r (s,cr) -> if ConstraintSatisfied cr Ss then Set.add s r else r ) Ø t

let update x signs state =
    let rSet = Set.filter (fun (y,s) -> not (x=y) ) state
    Set.fold (fun rst sign -> Set.add (x,sign) rst ) rSet signs

let ruleSatisfied_s state (Policy(var,r)) =
    let SetOfVar = Set.fold(fun r (v,s) -> if var=v then Set.add s r else r) Ø state
    let rule = (ruleToSign r)
    if Set.isEmpty rule then Unknown
    else if Set.isSubset SetOfVar rule then Satisfied
    else if Set.isSuperset SetOfVar rule then Unknown
    else Unsatisfied

let f_s Ss (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  -> update x (Ac Ss fu) Ss
    | Node( Assign, Node(A(ar),l)::fu::[] ) -> update ar (Ac Ss fu+(Ac Ss (Node(A(ar),l)))) Ss
    | Node( Decl,   Node(X(x),_)::xs )      -> update x (Set.ofList [Zero]) Ss
    | Node( Decl,   Node(A(ar),l)::xs)      -> update ar ((Ac Ss (Node(A(ar),l)))+(Set.ofList [Zero])) Ss
    | Node( Send,   Node(C(ch),_)::x::xs)   -> update ch (Ac Ss x) Ss
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> update x (Ac Ss ch) Ss
    | Node( Recv,   ch::Node(A(ar),l)::xs)  -> update ar ( (Ac Ss ch) + (Ac Ss (Node(A(ar),l))) ) Ss
    | Node( b, _ ) when isBoolOp b          -> boolFilter Bs a Ss
    | _ -> Ss

let signToString = function
    | Pos  -> "+"
    | Neg  -> "-"
    | Zero -> "0"
    | S_Undefined -> "Err."

let framework_s cr G p =
    let l = Ls G
    let ex = exVal_s G p
    (f_s,l,ex,con_sa cr,con_sg cr,(policySats ruleSatisfied_s))
