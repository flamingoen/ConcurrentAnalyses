module CombinatorialAnalysis

open Defines

let L_cb (l1,l2) =
    let btm = Set.ofList [(Set.empty,Set.empty)]
    let top = Ø
    let lob S1 S2 = Set.(+) (S1,S2)
    (btm,top,lob)

let exVal_cb (ex1,ex2) = Set.ofList [(ex1,ex2)]

let Ca_cb (c1,c2) Ss t (cs1,cs2) =
    Set.fold(fun (r1,r2) (S1,S2) -> ((c1 S1 t r1),(c2 S2 t r2)) ) (cs1,cs2) Ss

let Cg_cb (c1,c2) id Ss (cs1,cs2) =
    Set.fold(fun r (S1,S2) -> Set.add ((c1 id S1 cs1),(c2 id S2 cs2)) r ) Ø Ss

let P_cb (p1:(policies -> 'a -> policyList),p2) p s =
    let t = Set.fold (fun r (s1,s2) -> pl_xor ((pl_plus ((p1 p s1),(p2 p s2))),r) ) (toPolicyList Satisfied p) s
    printfn"%A\n%A\n" s t
    t

let f_cb f1 f2 Ss t = Set.fold(fun r (S1,S2) -> Set.add (f1 S1 t,f2 S2 t) r ) Ø Ss
