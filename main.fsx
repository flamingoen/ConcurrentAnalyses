#r "FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll"

open System
open System.IO

type analysisType = RD | LV | DOS | DOI | PAR

printfn""
let stopWatch = System.Diagnostics.Stopwatch.StartNew()
#load "defines.fs";
#load "lexerParser/GuardedCommandParser.fs"
#load "lexerParser/GuardedCommandLexer.fs"
#load "programs.fs"
#load "compiler/treeGenerator.fs"
#load "compiler/programGraphs.fs"
#load "graphviz/graphViz.fs"
#load "analyses/policies.fs"
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

stopWatch.Restart()
open Programs
open ProgramGraphs
open TreeGenerator
open GraphViz
open Analysis
stopWatch.Stop()
printfn "Open time:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

let program = multiplex
let analysisType = DOI
open Policies
let policy = [("in1",R_Eq(10))]

stopWatch.Restart()
let syntaxTree =
    try parse program
    with e -> failwith ("could not parse program:\n"+program)

let (graph,ex) = ( pgGen syntaxTree )
let (G,E) = (normalizeGraph graph ex)
let (graphProduct,exValProduct) = productGraph G E
printfn "Compile time:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

// GRAPHVIZ
stopWatch.Restart()
makeGraph G E
//makeProductGraph graphProduct e
printfn "Graphviz:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

stopWatch.Restart()
let run g e p = function
    | RD  ->
        reachingDefinition g e -1
    | LV  ->
        liveVariables g e
    | DOS ->
        detectionOfSignsAnalysis g p e
    | DOI ->
        intervalAnalysis g p e
    | PAR ->
        parityAnalysis g p e

run G E policy analysisType
printfn "Analysis time: %f ms" stopWatch.Elapsed.TotalMilliseconds
