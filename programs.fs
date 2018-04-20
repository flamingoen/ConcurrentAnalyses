module Programs

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

let bakery2 = "
par
    do true ->
        x1 := x2 + 1;
        if x2 = 0 | x1 < x2 -> skip fi;
        x2 := 0
    od
[]
    do true ->
        x2 := x1 + 1;
        if x1 = 0 | x2 < x1 -> skip fi;
        x1 := 0
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
    in1!10
[]
    in2!-10
[]
    var x;
    if true -> in1?x; skip
    [] true -> in2?x; x:=x- 1; skip
    fi;
    skip;
    ch!x*2
[]
    var z;
    ch?z;
    if z%2=0 -> out!z/2
    [] z%2=1 -> out!z/2- 1
    fi
rap
"

let temp = "
par
    in1!1
[]
    in2!-1
[]
    var x;
    if true -> in1?x; ch!2*x
    [] true -> in2?x; ch!2*x-1
    fi
[]
    var z;
    if z%2=0 -> out!z/2
    [] z%2=1 -> out!z/2
    fi
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
