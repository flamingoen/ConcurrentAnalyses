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

let run prog pol atype =
    let syntaxTree = try parseProgram prog with e -> failwith ("could not parse program:\n"+prog)
    let p = try parsePolicy pol with e -> failwith ("Could not parse policy:\n"+pol)
    let (g,e) = normalizeGraph ( pgGen syntaxTree )
    makeGraph g e
    //let (graphProduct,exValProduct) = productGraph G E
    //makeProductGraph graphProduct e
    match atype with
    | RD  -> reachingDefinition g e -1
    | LV  -> liveVariables g e
    | DOS -> detectionOfSignsAnalysis g p e
    | DOI -> intervalAnalysis g p e
    | PAR -> parityAnalysis g p e


// ##### Running everything ######
let program = shifter
let analysisType = DOI
let pol = " x > -1 y > -1 x<2 y<2 "

stopWatch.Restart()
run program pol analysisType
stopWatch.Stop()
printfn "\nAnalysis time: %f ms" stopWatch.Elapsed.TotalMilliseconds
