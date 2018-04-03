module graphViz
open GC

let rec nodeToString = function
    | Node(X(var),[])           -> var
    | Node(N(int),[])           -> string int
    | Node(A(arr),a::[])        -> arr + "["+(nodeToString a)+"]"
    | Node(C(ch),[])            -> ch
    | Node(Decl,x::[])          -> ("var "+nodeToString x)
    | Node(a,a1::a2::[]) when (op.ContainsKey a) ->
        (nodeToString a1) + op.[a] + (nodeToString a2)
    | Node(Skip,[])             -> "skip"
    | Node(True,[])             -> "true"
    | Node(False,[])            -> "false"
    | Node(Not,[Node(True,_)])  -> "false"
    | Node(Not,[Node(False,_)]) -> "true"
    | Node(Not,c::[])           -> "!(" + (nodeToString c)+")"
    | Node(Assign,x::a::[])     -> (nodeToString x) + ":=" + (nodeToString a)
    | Node(Send,ch::a::[])      -> (nodeToString ch) + "!" + (nodeToString a)
    | Node(Recv,ch::a::[])      -> (nodeToString ch) + "?" + (nodeToString a)
    | Node(action,_)            -> failwith ((string action)+" could not be converted")

let labelToString set = Set.fold (fun rst (q:int) -> rst+"q"+(string q)) "" set

let rec graphToGraphviz = function
    | []               -> ""
    | (qs,tree,qt,id)::xs ->
        "" + (labelToString qs) + " -> " + (labelToString qt) + " [label = \""+(nodeToString tree)+"\"];\n"  + (graphToGraphviz xs)

let generateInitVals inits =
    let header = "node [shape = circle, fillcolor=PaleGreen3];"
    let nodeString = Set.fold (fun rst q -> q+";"+rst) "" inits
    header + nodeString + "\n"
    ;;

let generateEndVals ends =
    let header = "node [shape = doublecircle fillcolor=SkyBlue2, style=filled];"
    let nodeString = Set.fold (fun rst q -> q+";"+rst) "" ends
    header + nodeString + "\n"
    ;;

let printGraphviz path graph initVals endVals =
    let header = "digraph program_graph {rankdir=LR;\n"
    let endNodes = ( generateEndVals endVals )
    let initNodes = ( generateInitVals initVals )
    let nodes = "node [shape = circle, fillcolor=LightGray]"
    let graphviz = (header+endNodes+initNodes+nodes+(graphToGraphviz graph)+"}")
    File.WriteAllText(path, graphviz) ;;

let makeProductGraph graph exVal =
    let path = "graphviz/productGraph.gv"
    let initVal = (Set.add (List.fold (fun rst ((qs:int),qt,_) -> rst+"q"+(string qs) ) "" exVal) Set.empty )
    let endVal = (Set.add (List.fold (fun rst (qs,(qt:int),_) -> rst+"q"+(string qt) ) "" exVal) Set.empty )
    printGraphviz path graph initVal endVal

let makeGraph graph exVal =
    let path = "graphviz/graph.gv"
    let initVals = List.fold (fun rst ((qs:int),qt,_) -> Set.add ("q"+(string qs)) rst ) Set.empty exVal
    let endVals = List.fold (fun rst (qs,(qt:int),_) -> Set.add ("q"+(string qt)) rst ) Set.empty exVal
    let setisfyedGraph = List.fold (fun rst (qs:int,a,qt:int,id) -> ((Set.ofList [qs]),a,(Set.ofList [qt]),id)::rst) [] graph
    printGraphviz path setisfyedGraph initVals endVals
