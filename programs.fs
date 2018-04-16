module programs

let simpleProgram = "
par x:=1 [] x:=-1 rap
"

let testProgram2 = "
par
    x:=0;
    y:=0;
    if
        true -> x:=1; skip
    []
        true -> x:=-1; skip
    fi
[]
    x:=0;
    if
        x>0 -> y:=1
    []
        true -> y:=-1
    fi;
    skip
rap
"

let bakeryAlgorithm = "
par
    do true ->
        x := y + 1;
        if
            y = 0 | x < y -> skip
        []
            ~(y = 0) & ~(x < y) -> skip
        fi;
        x := 0
    od
[]
    do true ->
        y := x + 1;
        if
            x = 0 | y < x -> skip
        []
            ~(x = 0) & ~(y < x) -> skip
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

let multiplex_loop = "
par
    var x; var y;
    do true ->
        cx?x;
        cy?y;
        c!y
    od
[]
    do true -> cy!1; cx!1
    [] true -> cy!-1; cx!-1
    od
[]
    var x;
    do true -> c?x od
rap
"

let multiplex = "
par
    var y;
    c1?y;
    c2!y
[]
    var x;
    if true -> x:=1
    [] true -> x:=-1
    fi;
    c1!x
[]
    var z;
    c2?z
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
    n := 10;
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
