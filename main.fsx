#r "FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll"

open System
open System.IO

printfn""
let stopWatch = System.Diagnostics.Stopwatch.StartNew()
#load "GC.fs";
#load "GuardedCommandParser.fs"
#load "GuardedCommandLexer.fs"
#load "programs.fs"
#load "treeGenerator.fs"
#load "programGraphs.fs"
#load "graphViz.fs"
#load "lattice.fs"
#load "bitVectorAnalyses.fs"
#load "tablesSign.fs"
#load "constraintAnalysis.fs"
#load "signAnalysis.fs"
#load "intervalAnalysis.fs"
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

let program = testProgram2

stopWatch.Restart()
let syntaxTree =
    try parse program
    with e -> failwith ("could not parse program:\n"+program)

let (graph,ex) = ( pgGen syntaxTree )
let (G,e) = (normalizeGraph graph ex)
//let (graphProduct,exValProduct) = productGraph G e
printfn "Compile time:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

// GRAPHVIZ
stopWatch.Restart()
makeGraph G e
//makeProductGraph graphProduct e
printfn "Graphviz:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

stopWatch.Restart()
// REACHING DEFINITION
//reachingDefinition G e -1
//reachingDefinition graphProduct exValProduct (Set.ofList [-1])

// LIVE VARIABLES
//liveVariables G e
//liveVariables graphProduct exValProduct

// DETECTION OF SIGNS
//detectionOfSignsAnalysis G e
//detectionOfSignsAnalysis graphProduct exValProduct

// INTERVAL ANALYSIS
intervalAnalysis G e

printfn "Analysis time: %f ms" stopWatch.Elapsed.TotalMilliseconds
