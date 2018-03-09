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
#load "analysis.fs"
open analysis

let syntaxTree = parse bakeryAlgorithm

let (graph,exVal) = ( pgGen syntaxTree )

//let rec QC i map = function
//    | []          -> map
//    | nodes::rst  -> QC (i+1) (Set.fold (fun rst node -> Map.add node i rst) map nodes) rst
//
//let C = (components graph (allNodes graph))
//printList C
//printMap (QC 0 Map.empty (components graph (allNodes graph)))

makeGraph graph exVal
#time
reachingDefinition graph exVal -1
#time

//let (graphProduct,exValProduct) = productGraph graph exVal
//makeProductGraph graphProduct exVal
//#time
//reachingDefinition graphProduct exValProduct (Set.ofList [-1])
//#time
