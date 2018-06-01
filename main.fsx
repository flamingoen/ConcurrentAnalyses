#r "FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll"

open System
open System.IO
type analysisType = RD | LV | DOS | DOI | PAR

printfn""
let stopWatch = System.Diagnostics.Stopwatch.StartNew()
#r "dlls/defines.dll"
#r "dlls/LexerParser.dll"
#r "dlls/compiler.dll"
#load "programs.fs"
#load "graphviz/graphViz.fs"
#load "analyses/bitVectorAnalyses.fs"
#load "analyses/tablesSign.fs"
#load "analyses/integerAnalysis.fs"
#load "analyses/constraintAnalysis.fs"
#load "analyses/signAnalysis.fs"
#load "analyses/intervalAnalysis.fs"
#load "analyses/parityAnalysis.fs"
#load "worklistAlgorithm.fs"
#load "analysis.fs"
stopWatch.Stop()
printfn "load time:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

open Programs
open ProgramGraphs
open PolicyGenerator
open TreeGenerator
open GraphViz
open Analysis

let run prog pol atype product =
    let syntaxTree = try parseProgram prog with e -> failwith ("could not parse program:\n"+prog)
    let p = try parsePolicy pol with e -> failwith ("Could not parse policy:\n"+pol)
    printfn"%A" p
    let (g,e) = normalizeGraph ( pgGen syntaxTree )
    makeGraph g e
    let (gp,ep) = productGraph g e
    makeProductGraph gp e
    match atype with
    | RD  when product -> reachingDefinition gp ep (Set.ofList [-1])
    | RD  -> reachingDefinition g e -1
    | LV  when product -> liveVariables gp ep
    | LV  -> liveVariables g e
    | DOS when product -> detectionOfSignsAnalysis gp p ep
    | DOS -> detectionOfSignsAnalysis g p e
    | DOI when product -> intervalAnalysis gp p ep
    | DOI -> intervalAnalysis g p e
    | PAR when product -> parityAnalysis gp p ep
    | PAR -> parityAnalysis g p e


// ##### Running everything ######
let program = testProgram2
let analysisType = PAR
let pol = "
y<0 V x>0
"
let useProduct = false

stopWatch.Restart()
run program pol analysisType useProduct
stopWatch.Stop()
printfn "\nAnalysis time: %f ms" stopWatch.Elapsed.TotalMilliseconds
