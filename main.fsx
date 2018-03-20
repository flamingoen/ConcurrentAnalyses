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
#load "analysis.fs"
open analysis

let program = bakeryAlgorithm

let syntaxTree =
    try parse program
    with e -> failwith ("could not parse program:\n"+program)

let (graph,ex) = ( pgGen syntaxTree )
let (graphProduct,exValProduct) = productGraph graph ex

// GRAPHVIZ
makeGraph graph ex
makeProductGraph graphProduct ex

// REACHING DEFINITION
//#time
//reachingDefinition graph ex -1
//#time
//#time
//detectionOfSignsAnalysis graphProduct exValProduct (Set.ofList [-1])
//#time


// DETECTION OF SIGNS
#time
detectionOfSignsAnalysis graph ex
#time
//#time
//detectionOfSignsAnalysis graphProduct exValProduct
//#time
