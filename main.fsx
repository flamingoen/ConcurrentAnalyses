#r "FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll"

open System
open System.IO

// PARSE/LEX
#load "GC.fs"
open GC
#load "GuardedCommandParser.fs"
#load "GuardedCommandLexer.fs"
// GRAPH GENERATOR
#load "programs.fs"
#load "treeGenerator.fs"
#load "programGraphs.fs"
open programs
open programGraphs
open treeGenerator
// GRAPHICAL OUTPUT
#load "graphViz.fs"
open graphViz
// ANALYSES
#load "lattice.fs"
#load "bitVectorAnalyses.fs"
#load "tablesSign.fs"
#load "signAnalysis.fs"
#load "worklistAlgorithm.fs"
#load "analysis.fs"
open analysis

let program = testProgram2

let syntaxTree =
    try parse program
    with e -> failwith ("could not parse program:\n"+program)

let (graph,ex) = ( pgGen syntaxTree )
let (G,e) = (normalizeGraph graph ex)
let (graphProduct,exValProduct) = productGraph G e


// GRAPHVIZ
makeGraph G e
makeProductGraph graphProduct e

// REACHING DEFINITION
//#time
//reachingDefinition G e -1
//#time
//#time
//reachingDefinition graphProduct exValProduct (Set.ofList [-1])
//#time


// LIVE VARIABLES
//#time
//liveVariables G e
//#time
//#time
//liveVariables graphProduct exValProduct
//#time

// DETECTION OF SIGNS
#time
detectionOfSignsAnalysis G e
#time
//#time
//detectionOfSignsAnalysis graphProduct exValProduct
//#time
