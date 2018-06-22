module BitVectorAnalyses

open Defines
open ProgramGraphs

let BVF kill gen state t = (Set.difference state (kill state t)) + (gen t)

let con_BVFg id Ss c = Map.fold (fun rst id' s -> if id'=id then rst else rst+s ) Ø c

let con_BVFa genf (s':Set<_>) (qs,a,qt,id) c =
    let gen = genf (qs,a,qt,id)
    match Map.tryFind id c with
    | Some(s) -> Map.add id (Set.(+) (s,gen)) c
    | None    -> Map.add id gen c

let combine x s = Set.fold (fun rst y -> Set.add (x,y) rst ) Set.empty s

// #### REACHING DEFINITIONS ####

let L_RD G = (Ø,(fun s1 s2 -> Set.(+) (s1,s2)))

let exVal_RD G non =
    Set.fold (fun rst var ->
        Set.add (var,non,non) rst
    ) Ø (removeLocalVars (varsInGraph G))

let kill_RD state (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      -> Set.filter (fun (var,q1,q2) -> var=x ) state
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.filter (fun (var,q1,q2) -> var=x ) state
    | Node( Decl,   Node(A(arr),_)::xs )    -> Set.filter (fun (var,q1,q2) -> var=arr ) state
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.filter (fun (var,q1,q2) -> var=x ) state
    | _ -> Set.empty

let gen_RD (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::xs )      -> Set.ofList [(x,qs,qt)]
    | Node( Assign, Node(A(arr),_)::xs )    -> Set.ofList [(arr,qs,qt)]
    | Node( Decl,   Node(X(x),_)::xs )      -> Set.ofList [(x,qs,qt)]
    | Node( Recv,   ch::Node(X(x),_)::xs)   -> Set.ofList [(x,qs,qt)]
    | _ -> Set.empty

let f_RD state t = BVF (kill_RD) (gen_RD) state t



// #### Live variables ####

let lob_LV s1 s2 = Set.(+) (s1,s2)
let L_LV = (Ø,lob_LV)
let exVal_LV = Set.empty

let rec FV = function
    | Node(A(x),_) when isLocal x  -> Set.ofList [x]
    | Node(A(x),_)                 -> Set.ofList [x]
    | Node(X(x),_)                 -> Set.ofList [x]
    | Node(X(x),_) when isLocal x  -> Set.ofList [x]
    | Node(_,lst)                  -> List.fold (fun rst x -> rst + (FV x)) Set.empty lst

let kill_LV state (qs,a,qt,id) =
    match a with
    | Node( Assign, Node(X(x),_)::xs )   -> Set.filter (fun (var) -> var=x ) state
    | Node( Decl,   Node(X(x),_)::xs )   -> Set.filter (fun (var) -> var=x ) state
    | Node( Decl,   Node(A(arr),_)::xs ) -> Set.filter (fun (var) -> var=arr ) state
    | _                                  -> Set.empty

let gen_LV (qs,a,qt,id) =
    match a with
    | Node( Assign, x::arthm::xs )  -> FV arthm
    | Node( Send,   ch::arthm::xs)  -> FV arthm
    | _ -> Set.empty

let f_LV state t = BVF (kill_LV) (gen_LV) state t
