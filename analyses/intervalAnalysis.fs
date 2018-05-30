module IntervalAnalysis

open Defines
open ConstraintAnalysis
open IntegerAnalysis
open ProgramGraphs

let MAX = 100
let MIN = -100

let ob_I = I(MAX,MIN)
let lb_I = Undefined

let btm_I = Ø
let top_I G = Set.fold (fun rst var -> Set.add (var,ob_I) rst ) Ø (varsInGraph G)

let lob_I s1 s2 =
     let map = Set.fold (fun rst (var,(i:interval)) -> Map.add var i rst ) Map.empty s1
     let newMap = Set.fold (fun rst (var,i) ->
         match Map.tryFind var map with
         | None -> (Map.add var i rst)
         | Some(i') -> Map.add var (i+i') rst ) map s2
     Map.fold (fun rst var i -> Set.add (var,i) rst ) Ø newMap

let L_I G = (btm_I,(top_I G),lob_I)

let intervalOf x state = Set.fold (fun r (v,i) -> if v=x then r+i else r ) Empty state

let ruleToInterval state = function
    | R_Pl      -> I(MAX,(max 1 MIN))
    | R_Mi      -> I((min -1 MAX),MIN)
    | R_Zr      -> I(0,0)
    | R_Grt(n)  -> I( MAX , (min (max (n+1) MIN) MAX) )
    | R_Lt(n)   -> I( (max (min (n-1) MAX) MIN) , MIN )
    | R_Eq(n)   -> I(n,n)
    | R_Grtx(x) -> (intervalOf x state)+I(MAX,MAX)
    | R_Ltx(x)  -> (intervalOf x state)+I(MIN,MIN)
    | R_Eqx(x)  -> intervalOf x state
    | _         -> ob_I

let exVal_I G p =
    let vars = (removeLocalVars (varsInGraph G)) + (channelsInGraph G)
    let policyMap = List.fold (fun xs (Policy(v,r)) ->
        match Map.tryFind v xs with
        | Some(i) -> Map.add v (i-(ruleToInterval (top_I G) r)) xs
        | None    -> Map.add v (ruleToInterval (top_I G) r) xs ) Map.empty p
    let polic = Map.fold (fun xs v i ->
        if Set.contains v vars then
            Set.add (v,i) xs
        else xs ) Ø policyMap
    let exclVars = (List.fold (fun xs (Policy(v,r)) -> Set.add v xs ) Ø p)+ (channelsInGraph G)
    Set.fold (fun rst var -> (Set.ofList [(var,ob_I)])+rst) polic (vars-exclVars)

let plus = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (I(mx,mn),I(mx',mn')) -> I( (min (mx+mx') MAX ), (max (mn+mn') MIN) )
    | (_,_)                 -> Empty
let minus  = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (I(mx,mn),I(mx',mn')) -> I( (min (mx-mn') MAX ), (max (mn-mx') MIN ) )
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
        let first = if mx=MAX || mx'=MAX then MAX else min (max (max (mx/mn') (mx/mx') ) (max (mn/mx') (mn/mn') )) MAX
        let second = if mn=MIN || mn'=MIN then MIN else max (min (min (mx/mn') (mx/mx') ) (min (mn/mx') (mn/mn') )) MIN
        I(first,second)
    | (_,_)                 -> Empty
let modulo = function
    | (Undefined,_)         -> Undefined
    | (_,Undefined)         -> Undefined
    | (_,I(0,0))            -> Undefined
    | (I(0,0),_)            -> I(0,0)
    | (I(mx,mn),I(mx',mn')) ->
        let first = if mx=MAX || mx'=MAX then MAX else min (max (max (mx%mn') (mx%mx') ) (max (mn%mx') (mn%mn') )) MAX
        let second = if mn=MIN || mn'=MIN then MIN else max (min (min (mx%mn') (mx%mx') ) (min (mn%mx') (mn%mn') )) MIN
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
    | (I(mx,mn),I(mx',mn')) when mx'<mn && mn'<mn -> Set.ofList [False]
    | (I(mx,mn),I(mx',mn')) when mx'>mx && mn'>mx -> Set.ofList [False]
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
    | (I(mx,mn),I(mx',mn')) when mn>mx'  -> Set.ofList [False]
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

let ConstraintSatisfied cr Ss =
    if Set.isEmpty cr then true
    else Set.fold (fun r' inner -> r' || Set.fold (fun r cnstr -> (Set.contains True (B_I Ss cnstr)) && r) true inner ) false cr

let con_ig cr id Ss c =
    let t = Map.fold (fun r id' s -> if id'=id then r else r+s ) Ø c
    Set.fold(fun r (s,cr) -> if ConstraintSatisfied cr Ss then Set.add s r else r ) Ø t

let con_ia cr Ss (qs,a,qt,id) c =
    let t = match a with
                | Node( Assign, Node(X(x),_)::fu::[] )  -> (x,(A_I Ss fu))
                | Node( Assign, Node(A(ar),l)::fu::[] ) -> (ar,(A_I Ss fu))
                | Node( Decl,   Node(X(x),_)::xs )      -> (x,I(0,0))
                | Node( Decl,   Node(A(ar),l)::xs)      -> (ar,I(0,0))
                | Node( Send,   Node(C(ch),_)::x::xs)   -> (ch,(A_I Ss x))
                | Node( Recv,   ch::Node(X(x),_)::xs)   -> (x,(A_I Ss ch))
                | Node( Recv,   ch::Node(A(ar),l)::xs)  -> (ar,(A_I Ss ch))
                | _                                     -> ("",Empty)
    let s' = if t = ("",Empty) then Ø else Set.ofList [(t,(Map.find qs cr))]
    match Map.tryFind id c with
        | Some(s) -> Map.add id (Set.union s' s) c
        | None    -> Map.add id s' c

let update x interval c state =
    let rSet = Set.filter (fun (v,i) -> not (v=x) ) state
    Set.add (x,interval) rSet

let splitIntervalSet s inter = Set.fold (fun rst (v,i) ->
    match i with
    | I(mx,mn) -> (List.fold (fun rst' j -> Set.add (v,I((min (j+inter) mx),j)) rst' ) Ø [mn ..inter.. mx])+rst
    | _          -> Set.add (v,i) rst ) Ø s

let mergeIntervalSet s = Set.fold (fun rst e -> lob_I (Set.ofList [e]) rst) Ø s

let f_I splitInterval Ss (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  -> update x (A_I Ss fu) Ø Ss
    | Node( Assign, Node(A(ar),l)::fu::[] ) -> update ar ((A_I Ss fu)+(A_I Ss (Node(A(ar),l)))) Ø Ss
    | Node( Decl,   Node(X(x),_)::xs )      -> update x (I(0,0)) Ø Ss
    | Node( Decl,   Node(A(ar),l)::xs)      -> update ar (I(0,0)) Ø Ss
    | Node( Send,   Node(C(ch),_)::x::xs)   -> update ch (A_I Ss x) Ø Ss
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> update x (A_I Ss ch) Ø Ss
    | Node( Recv,   ch::Node(A(ar),l)::xs)  -> update ar ((A_I Ss ch)+(A_I Ss (Node(A(ar),l)))) Ø Ss
    | Node( b, _ ) when isBoolOp b          -> mergeIntervalSet (boolFilter B_I a (splitIntervalSet Ss splitInterval))
    | _ -> Ss

let p_I p s =
    List.forall (fun (Policy(v,r)) ->
        let rule = (ruleToInterval s r)
        let exists = Set.fold (fun xs (v',i) -> v=v' || xs ) false s
        Set.fold (fun xs (v',i) -> v=v' && (Set.contains True (equal (i,rule)) ) || xs ) (not exists) s ) p

// (Set.contains True (equal (i,rule)) )
// (rule+i = rule)

let intervalToString = function
    | Undefined  -> "Err"
    | Empty      -> "?"
    | I(max,min) when max=MAX && min=MIN -> "( -∞ : ∞ )"
    | I(max,min) when max=MAX            -> "( "+(string min)+" : ∞ )"
    | I(max,min) when min=MIN            -> "( -∞ : "+(string max)+" )"
    | I(max,min)                         -> "( "+(string min)+" : "+(string max)+" )"
