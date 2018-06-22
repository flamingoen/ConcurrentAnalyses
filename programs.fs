module Programs

let simpleProgram = "
par x:=2 [] x:= -1 rap
"

let testProgram2 = "
par
    if
        true -> x:=1; skip
    []
        true -> x:=-1; skip
    fi
[]
    if
        x>0 -> y:=1
    []
        true -> y:=-1
    fi
rap
"

let badBakery = "
par
    var x;
    loop
        c1 := c2*(-1);
        do c2 > 0 -> c1 := c2*(-1) od;
        in1?x;
        x := x*2 - 1;
        out!x;
        c1 := -1
    pool
[]
    var x;
    loop
        c2 := c1*(-1);
        do c1 > 0 -> c2 := c1*(-1) od;
        in2?x;
        x := x*2;
        out!x;
        c2 := -1
    pool
[]
    var b;
    var r;
    loop
        out?r;
        b := r%2;
        if b=0 -> skip [] b>0 -> skip fi
    pool

rap
"

let badBakerySimple = "
par
    loop
        c1 := c2*(-1);
        do c2 > 0 -> c1 := c2*(-1) od;
        skip;
        c1 := -1
    pool
[]
    loop
        c2 := c1*(-1);
        do c1 > 0 -> c2 := c1*(-1) od;
        skip;
        c2 := -1
    pool
rap
"

let badBakeryMod = "
par
    loop
        c1 := c2*(-1);
        if c1 > 0 & c2 < 0 -> crit; c1 := -1
        [] c1 <= 0 & c2 >= 0 -> skip fi
    pool
[]
    loop
        c2 := c1*(-1);
        if c1 < 0 & c2 > 0 -> crit; c2 := -1
        [] c1 >= 0 & c2 <= 0 -> skip fi
    pool
rap
"

let goodBakery = "
par
    loop
        c1 := c2+1;
        do c2 = 0 | c1>c2 -> skip od;
        crit;
        c1 := 0
    pool
[]
    loop
        c2 := c1+1;
        do c1 = 0 | c2>c1 -> skip od;
        crit;
        c2 := 0
    pool
rap
"

let securityBakery = "
par
    var x;
    loop
        c1 := c2+1;
        do c2 = 0 | c1>c2 -> skip od;
        in1?x;
        x := (x - 1) * 2;
        out!x;
        c1 := 0
    pool
[]
    var x;
    loop
        c2 := c1+1;
        do c1 = 0 | c2>c1 -> skip od;
        in2?x;
        x := x*2;
        out!x;
        c2 := 0
    pool
[]
    var r;
    loop
        out?r;
        if r%2=0 -> crit [] r%2>0 -> crit fi
    pool
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
    var x;
    if true -> in1?x
    [] true -> in2?x; x:=x- 1
    fi;
    ch!x*2
[]
    var z;
    ch?z;
    if z%2=0 -> out!z/2
    [] z%2=1 -> z:=z/2; out!z+1
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

let shifter = "
par
    loop true ->
        if x>y -> y := x + 1 fi
    pool
[]
    loop true ->
        if y>x -> y := x - 1 fi
    pool
rap
"
