module Defines

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

// ##### LATTICE #####
type Lattice<'a when 'a : comparison> = Set<'a> * Set<'a> * Set<'a> -> Set<'a> -> Set<'a> ;;

let btm (b,t,o) = b ;;
let top (b,t,o) = t ;;
let lob s1 s2 (b,t,o) = o s1 s2 ;;
let subeq s1 s2 (b,t,o) = (o s1 s2 ) = s2 ;;
let supeq s1 s2 (b,t,o) = (o s1 s2 ) = s1 ;;
let sup s1 s2 L = not (subeq s1 s2 L)
let sub s1 s2 L = not (supeq s1 s2 L)

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

let magic s1 s2 op = Set.fold (fun rst e1 ->
    (Set.fold (fun rst' e2 -> rst'+(op (e1,e2))) Set.empty s2)+rst ) Set.empty s1

let Ø = Set.empty

// ####### ANALYSIS TYPES #######
type sign = Pos | Neg | Zero
type parity = Even | Odd
type interval =
    I of (int*int) | Undefined | Empty
    static member (+) (e1:interval,e2:interval) =
        match (e1,e2) with
        | (Undefined,_) -> Undefined
        | (_,Undefined) -> Undefined
        | (Empty,i)     -> i
        | (i,Empty)     -> i
        | (I(mx,mn),I(mx',mn')) -> I((max mx mx'),(min mn mn'))
