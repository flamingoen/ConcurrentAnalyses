module CombinatorialAnalysis

open Defines

let L_cb (l1,l2) =
    let btm = Ø
    let lob S1 S2 = Set.(+) (S1,S2)
    (btm,lob)

let exVal_cb (ex1,ex2) = Set.ofList [(ex1,ex2)]

let Ca_cb (c1,c2) Ss (qs,a,qt,id) cs =
    let t = (qs,a,qt,id)
    let s' = Set.fold(fun r (S1,S2) ->
        let con1 = Map.find id (c1 S1 t Map.empty)
        let con2 = Map.find id (c2 S2 t Map.empty)
        if (Set.isEmpty con1) && (Set.isEmpty con2) then r else Set.add (con1,con2) r ) Ø Ss
    match Map.tryFind id cs with
        | Some(s)                    -> Map.add id (Set.union s s') cs
        | None when (Set.isEmpty s') -> cs
        | None                       -> Map.add id s' cs

let Cg_cb (c1,c2) id Ss cs =
    let (t1,t2) = Map.fold (fun (r1,r2) id' s ->
        let (s1,s2) = Set.fold (fun (r1',r2') (s1',s2') -> (r1'+s1',r2'+s2')) (Ø,Ø) s
        if id'=id then (r1,r2) else ((r1+s1),(r2+s2)) ) (Ø,Ø) cs
    let (cs1,cs2) = (Map.add (id+1) t1 Map.empty , Map.add (id+1) t2 Map.empty)
    Set.fold (fun r (ss1,ss2) ->  Set.add (c1 id ss1 cs1,c2 id ss2 cs2) r  ) Ø Ss

let P_cb (p1:(policies -> 'a -> (policyList List)),p2) p s =
    Set.fold (fun r (s1,s2) ->
        let ps1 = (p1 p s1)
        let ps2 = (p2 p s2)
        let plp = pl_plus (ps1,ps2)
        let plc = pl_concatOr plp
        pl_and (plc,r) ) (pl_concatOr (toPolicyList Satisfied p)) s

let f_cb f1 f2 Ss t = Set.fold(fun r (S1,S2) -> Set.add (f1 S1 t,f2 S2 t) r ) Ø Ss
