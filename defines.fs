module Defines

// ##### DEFINITIONS #####
type action = N of int | X of string | A of string | C of string | Assign | P | Cp | Decl | Seq | Send | Recv | Skip | Crit | If | Loop | Do | Gc | Guard | True | False | Pl | Mi | Mlt | Div | Mod | Gt | Lt | Eq | Geq | Leq | Neq | Not | Land | Lor;;
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
type lattice<'a when 'a : comparison> = Set<'a> * Set<'a> * (Set<'a> -> Set<'a> -> Set<'a>)
let btm (b,t,u) = b
let top (b,t,u) = t
let lob s1 s2 (b,t,u) = u s1 s2
let subeq s1 s2 (b,t,u) = (u s1 s2) = s2
let supeq s1 s2 (b,t,u) = (u s1 s2) = s1
let sup s1 s2 L = not (subeq s1 s2 L)
let sub s1 s2 L = not (supeq s1 s2 L)

// ##### HELPERS ####
let printList list = List.iter (fun lst -> (printfn("%A") lst) ) list
let printMap map = Map.iter (fun key lst -> (printfn("%A\t->\t %A") key lst) ) map
let printSet set = Set.iter (fun elem -> (printfn("%A") elem) ) set
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
type sign = Pos | Neg | Zero | S_Undefined
type parity = Even | Odd | P_Undefined
type interval =
    I of (int*int) | Undefined | Empty
    static member (+) (e1:interval,e2:interval) =
        match (e1,e2) with
        | (Undefined,_) -> Undefined
        | (_,Undefined) -> Undefined
        | (Empty,i)     -> i
        | (i,Empty)     -> i
        | (I(mx,mn),I(mx',mn')) -> I((max mx mx'),(min mn mn'))
    static member (-) (e1:interval,e2:interval) =
        match (e1,e2) with
        | (Undefined,_) -> Undefined
        | (_,Undefined) -> Undefined
        | (Empty,i)     -> i
        | (i,Empty)     -> i
        | (I(mx,mn),I(mx',mn')) when mx'<mn && mn'<mn -> Undefined
        | (I(mx,mn),I(mx',mn')) when mx'>mx && mn'>mx -> Undefined
        | (I(mx,mn),I(mx',mn')) -> I((min mx mx'),(max mn mn'))
    static member (.-) (e1:interval,e2:interval) =
        match (e1,e2) with
        | (Undefined,_) -> Undefined
        | (_,Undefined) -> Undefined
        | (Empty,i)     -> i
        | (i,Empty)     -> i
        | (I(mx,mn),I(mx',mn')) when mx'<mn && mn'<mn -> I(mx',mn')
        | (I(mx,mn),I(mx',mn')) when mx'>mx && mn'>mx -> I(mx',mn')
        | (I(mx,mn),I(mx',mn')) when mn'<mn && mx'>mx -> I(mx',mn)
        | (I(mx,mn),I(mx',mn')) when mx>mx' && mn<mn' -> I(mx,mn)
        | (I(mx,mn),I(mx',mn')) when mn'>mn && mx'<mx -> Empty
        | (I(mx,mn),I(mx',mn')) when mx<mx' && mn>mn' -> Empty
        | _,_ -> Empty

// CONSTRAINTS

type constraints = Constraint of Set<Set<action>>


// POLICIES

type rule = R_Pl | R_Mi | R_Zr | R_Even | R_Odd | R_Grt of int | R_Lt of int | R_Eq of int | R_Grtx of string | R_Ltx of string | R_Eqx of string
type policy = Policy of (string * rule)
type policies = (policy List) List

type policyResult =
    Unknown | Satisfied | Unsatisfied | Error
    static member (.&) (e1:policyResult,e2:policyResult) =
        match (e1,e2) with
        | (Satisfied,Satisfied)     -> Satisfied
        | (Unsatisfied,_)           -> Unsatisfied
        | (_,Unsatisfied)           -> Unsatisfied
        | (_,_)                     -> Unknown
    static member (.|) (e1:policyResult,e2:policyResult) =
        match (e1,e2) with
        | (_,Satisfied)             -> Satisfied
        | (Satisfied,_)             -> Satisfied
        | (Unsatisfied,Unsatisfied) -> Unsatisfied
        | (_,_)                     -> Unknown
    static member (.+) (e1:policyResult,e2:policyResult) =
        match (e1,e2) with
        | (Unsatisfied,Satisfied)   -> Unknown
        | (Satisfied,Unsatisfied)   -> Unknown
        | (Satisfied,_)             -> Satisfied
        | (Unsatisfied,_)           -> Unsatisfied
        | (_,Satisfied)             -> Satisfied
        | (_,Unsatisfied)           -> Unsatisfied
        | (_,_)                     -> Unknown
    static member (.^) (e1:policyResult,e2:policyResult) =
        match (e1,e2) with
        | (Satisfied,Satisfied)       -> Satisfied
        | (Unsatisfied,Unsatisfied)   -> Unsatisfied
        | (_,_)                     -> Unknown

type policyList = policyResult List
let pl_plus (e1:policyList,e2:policyList)       = List.map2 (.+) e1 e2
let pl_concat (e:policyList)                    = List.fold (.&) Satisfied e
let pl_and (e1:policyList,e2:policyList)        = List.map2 (.&) e1 e2
let pl_xor (e1:policyList,e2:policyList)        = List.map2 (.^) e1 e2
let toPolicyList (s:policyResult)(e:policies)   = List.fold (fun r lst -> s::r) [] e

let p_true s = true

let orRule ruleSatisfied state pList =
    let ruleMap = List.fold (fun r (Policy(var,rule)) ->
        match Map.tryFind var r with
        | None -> Map.add var (Set.ofList [rule]) r
        | Some(s) ->  Map.add var (Set.add rule s) r ) Map.empty pList
    Map.fold(fun r var ruleSet ->
        (ruleSatisfied ruleSet var state) .| r) Unsatisfied ruleMap
let policySats rs p s = List.map(orRule rs s) p

let ruleToString = function
    | R_Pl -> "->+"
    | R_Mi -> "->-"
    | R_Zr -> "->0"
    | R_Odd -> "->odd"
    | R_Even -> "->even"
    | R_Grt(n) -> ">"+(string n)
    | R_Lt(n) -> "<"+(string n)
    | R_Eq(n) -> "="+(string n)
    | R_Grtx(x) -> ">"+x
    | R_Ltx(x) -> "<"+x
    | R_Eqx(x) -> "="+x


let policyToString = function
    Policy(var,rule) -> var+(ruleToString rule)
