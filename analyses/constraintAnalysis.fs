module ConstraintAnalysis

open Defines
open IntegerAnalysis
open ProgramGraphs

let op = [Gt; Lt; Eq; Geq; Leq; Neq; True; False]

let rec Bp tree =
    match tree with
    | Node(Not,b1::_)       -> Bpn b1
    | Node(Lor,b1::b2::_)   -> (Bp b1)+(Bp b2)
    | Node(Land,b1::b2::_)  ->
        Set.fold (fun r s -> (Set.fold (fun r' s' -> Set.add (s'+s) r' ) Ø (Bp b2)) + r ) Ø (Bp b1)
    | Node(a,_) when (List.contains a op) -> Set.add (Set.ofList [tree]) Ø
    | _     -> failwith("Unsupported action in Bp")
and Bpn tree =
    match tree with
    | Node(Not,b1::_)       -> Bp b1
    | Node(Lor,b1::b2::_)   -> Bp (Node(Land,[Node(Not,[b1]);Node(Not,[b2])]))
    | Node(Land,b1::b2::_)  -> Bp (Node(Lor,[Node(Not,[b1]);Node(Not,[b2])]))
    | Node(a,_) when (List.contains a op) -> Set.add (Set.ofList [Node(Not,[tree])]) Ø
    | _     -> failwith("Unsupported action in Bp")

let exVal_C evali = (evali,Ø)
let btm_C L G =
    let t = List.filter (fun (qs,Node(a,_),qt,id) -> List.contains a op) G
    let t' = List.fold (fun r (qs,b,qt,id) -> r + (Bp b) ) Ø t
    (btm L,t')
let lob_C L (s1,c1) (s2,c2) = ( (lob s1 s2 L) , (Set.intersect c1 c2) )
let Lc Ls G = (btm_C Ls G,lob_C Ls)

let Fc fi Bi (Si,Sc) (qs,a,qt,id) =
    match a with
    | Node( b, _ ) when isBoolOp b ->
        let Sc' = Set.filter ( Set.fold (fun r s -> r && not (Set.contains True (Bi Si s) ) ) true  ) (Bp a)
        (fi Si (qs,a,qt,id),Set.union Sc Sc')
    | _ -> (fi Si (qs,a,qt,id),Sc)
