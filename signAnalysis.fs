module signAnalysis

let plus = function
    | "-","-" -> Set.ofList ["-"]
    | "-","0" -> Set.ofList ["-"]
    | "-","+" -> Set.ofList ["-"; "0"; "+"]
    | "0","-" -> Set.ofList ["-"]
    | "0","0" -> Set.ofList ["0"]
    | "0","+" -> Set.ofList ["+"]
    | "+","-" -> Set.ofList ["-"; "0"; "+"]
    | "+","0" -> Set.ofList ["+"]
    | "+","+" -> Set.ofList ["+"]
    | _       -> failwith("wrong sign detected")

let multi = function
    | "-","-" -> Set.ofList ["+"]
    | "-","0" -> Set.ofList ["0"]
    | "-","+" -> Set.ofList ["-"]
    | "0","-" -> Set.ofList ["0"]
    | "0","0" -> Set.ofList ["0"]
    | "0","+" -> Set.ofList ["0"]
    | "+","-" -> Set.ofList ["-"]
    | "+","0" -> Set.ofList ["0"]
    | "+","+" -> Set.ofList ["+"]
    | _       -> failwith("wrong sign detected")

let minus = function
    | "-","-" -> Set.ofList ["-"; "0"; "+"]
    | "-","0" -> Set.ofList ["-"]
    | "-","+" -> Set.ofList ["-"]
    | "0","-" -> Set.ofList ["+"]
    | "0","0" -> Set.ofList ["0"]
    | "0","+" -> Set.ofList ["-"]
    | "+","-" -> Set.ofList ["+"]
    | "+","0" -> Set.ofList ["+"]
    | "+","+" -> Set.ofList ["-"; "0"; "+"]
    | _       -> failwith("wrong sign detected")

let divide = function
    | "-","-" -> Set.ofList ["+"]
    | "-","0" -> Set.empty
    | "-","+" -> Set.ofList ["-"]
    | "0","-" -> Set.ofList ["0"]
    | "0","0" -> Set.empty
    | "0","+" -> Set.ofList ["0"]
    | "+","-" -> Set.ofList ["-"]
    | "+","0" -> Set.empty
    | "+","+" -> Set.ofList ["+"]
    | _       -> failwith("wrong sign detected")

let btm_s = Set.empty ;;

let top_s = Set.empty ;;

let order_s s1 s2 = Set.(+) (s1,s2)

let exVal_s G = Set.empty
    //let vars = removeLocalVars (varsInGraph G)
    //Set.fold (fun rst var -> (Set.ofList [(var,"+",Global)])+rst) Set.empty vars

let con_S G cmps Aa q L =
    let distachedNodes = QQ q G cmps
    let CC = (Set.fold (fun rst q' -> rst + (Set.filter (fun (var,sign,origin) -> origin=Global ) (Map.find q' Aa)) ) Set.empty distachedNodes)
    Set.fold (fun rst (var,sign,origin) -> Set.add (var,sign,Concurrent) rst ) Set.empty CC


let signOf x sigma = Set.fold (fun rst (y,sign,o) -> if y=x then Set.add sign rst else rst ) Set.empty sigma

let magic s1 s2 op = Set.fold (fun rst e1 -> Set.fold (fun rst e2 -> rst+(op (e1,e2))) Set.empty s2) Set.empty s1

let rec As sigma = function
    | Node(X(x),_)          -> signOf x sigma
    | Node(A(arr),_)        -> signOf arr sigma
    | Node(C(ch),_)         -> signOf ch sigma
    | Node(N(0),_)          -> Set.ofList ["0"]
    | Node(N(n),_) when n>0 -> Set.ofList ["+"]
    | Node(N(n),_) when n<0 -> Set.ofList ["-"]
    | Node(Pl,a1::a2::_)    -> magic (As sigma a1) (As sigma a2) plus
    | Node(Mi,a1::a2::_)    -> magic (As sigma a1) (As sigma a2) minus
    | Node(Mlt,a1::a2::_)   -> magic (As sigma a1) (As sigma a2) multi
    | Node(Div,a1::a2::_)   -> magic (As sigma a1) (As sigma a2) divide
    | Node(a,_)             -> failwith("In As: unknown match for action "+(string a))

let rec Bs sigma = function
    | Node(True,_)          -> Set.ofList [True]
    | Node(False,_)         -> Set.ofList [False]
    | Node(a,_)             ->failwith("In Bs: unknown match for action "+(string a))

let update x signs sigma =
    let rSet = Set.filter (fun (y,s,o) -> not (x=y) ) sigma
    Set.fold (fun rst sign ->
        if isLocal x then Set.add (x,sign,Local) rst
        else Set.add (x,sign,Global) rst ) rSet signs

let f_s G cmps L Aa (qs,a,qt) =
    let sigma = (Map.find qs Aa)
    let con_qt = (con_S G cmps Aa qt L)
    match a with
    | Node( Assign, Node(X(x),_)::fu::[] )  -> (update x (As sigma fu) sigma) + con_qt
    | Node( Decl,   Node(X(x),_)::xs )      -> (update x (Set.ofList ["0"]) sigma) + con_qt
    | Node( Send,   Node(C(ch),_)::x::xs)   -> (update ch (As sigma x) sigma) + con_qt
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> (update x (As sigma ch) sigma) + con_qt
    | _ -> sigma + con_qt
