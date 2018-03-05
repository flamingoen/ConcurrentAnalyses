module programs

let testProgram = "
par
    do true -> x:=1 od
[]
    do true -> y:=1; skip od
rap
"

let myOwnVarsProgram = "
par
    var x;
    x:=4
[]
    var x;
    x:=10
rap
"

let doIfLoopProgram = "
par
    var x;
    do true -> x:=1 od
[]
    loop true -> x:=1 pool
[]
    if true -> x:=1 fi
rap
"

let simpleProgram = "
par x:=1 [] x:=-1 rap
"

let bakeryAlgorithm = "
par
    do true ->
        x := y + 1;
        if
            y == 0 || x < y -> skip
        []
            ~(y == 0) && ~(x < y) -> skip
        fi;
        x := 0
    od
[]
    do true ->
        y := x + 1;
        if
            x == 0 || y < x -> skip
        []
            ~(x == 0) && ~(y < x) -> skip
        fi;
        y := 0
    od
rap
"

let writeNoRead = "

par
    var x;
    do true -> ch?x od
[]
    do true -> skip od
rap

"

let writeNoReadConditional = "

par
    var x;
    do true -> chan?x od
[]
    var y;
    do
        y>0 -> chan!y
    od
rap

"

let moduloProgram = "
do m>=n -> m:=m-n od;
res := m
"

let gcdProgram = "
do m!=n ->
    if
        n>m -> n := n - m
    []
        n<=m -> m := m - n
    fi
od;
res := n
"

let fibonachi = "
    i := 0;
    j := 1;
    k := 1;
    do k<=n ->
        t := i + j;
        i := j;
        j :=  t;
        k := k + 1
    od;
    res := j
"
