#r "FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll"

open System
open System.IO
type analysisType = RD | LV | DOS | DOI | PAR

printfn""
let stopWatch = System.Diagnostics.Stopwatch.StartNew()
#load "defines.fs";
#load "programs.fs"
#load "lexerParser/GuardedCommandParser.fs"
#load "lexerParser/GuardedCommandLexer.fs"
#load "lexerParser/PoliciesParser.fs"
#load "lexerParser/PoliciesLexer.fs"
#load "compiler/treeGenerator.fs"
#load "compiler/programGraphs.fs"
#load "compiler/policyGenerator.fs"
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
open TreeGenerator
open PolicyGenerator
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
let program = fibonachi
let analysisType = DOI
let pol = " n > -1
            t > -1
            k > -1
            i > -1
            j > -1 "

stopWatch.Restart()
run program pol analysisType
stopWatch.Stop()
printfn "Analysis time: %f ms" stopWatch.Elapsed.TotalMilliseconds
