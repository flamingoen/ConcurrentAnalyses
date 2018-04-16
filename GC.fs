module GC

// ##### DEFINITIONS #####
type action = N of int | X of string | A of string | C of string | Assign | P | Cp | Decl | Seq | Send | Recv | Skip | If | Loop | Do | Gc | Guard | True | False | Pl | Mi | Mlt | Div | Mod | Gt | Lt | Eq | Geq | Leq | Neq | Not | Land | Lor;;
type tree = Node of action*tree list ;;
type origin = Global | Initial | Local | Concurrent
let op =
    [
    Pl,     "+";
    Mi,     "-";
    Mlt,    "*";
    Div,    "/";
    Mod,    "%";
    Eq,     "=";
    Lt,     "<";
    Gt,     ">";
    Leq,    "<=";
    Geq,    ">=";
    Neq,    "!=";
    Land,   " & ";
    Lor,    " | ";
    Send,   "!";
    Recv,   "?";
    ] |> Map.ofList ;;


// ##### HELPERS ####
let printList list = List.iter (fun lst -> (printfn("%A") lst) ) list ;;
let printMap map = Map.iter (fun key lst -> (printfn("%A\t->\t %A") key lst) ) map ;;
let printSet set = Set.iter (fun elem -> (printfn("%A") elem) ) set ;;
let foldSetList set = List.fold (fun rst s -> s+rst) Set.empty set

let isBoolOp b = List.contains b [Gt;Lt;Eq;Geq;Leq;Neq;Not;Land;Lor;True;False]

let rec subsets s =
    if Set.isEmpty s then Set.empty else
    let subset = Set.fold (fun rst e -> rst + (subsets (Set.remove e s)) ) Set.empty s
    Set.add s subset

let rec varsInA = function
    | Node(X(x),_) -> Set.ofList [x]
    | Node(_,lst) -> List.fold (fun rst a -> rst + (varsInA a)) Set.empty lst
    ;;

let magic s1 s2 op = Set.fold (fun rst e1 -> Set.fold (fun rst e2 -> rst+(op (e1,e2))) Set.empty s2) Set.empty s1

let Ø = Set.empty
