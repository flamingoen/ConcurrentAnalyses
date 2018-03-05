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

let syntaxTree = parse writeNoReadConditional
let (graph,exVal) = ( pgGen syntaxTree )
let (graphProduct,exValProduct) = productGraph graph exVal

makeProductGraph graphProduct exVal
makeGraph graph exVal

printfn("\n######## original graph ########")
#time
reachingDefinition graph exVal -1
#time

//printfn("\n######## Product graph ########")
//#time
//reachingDefinition graphProduct exValProduct (Set.ofList [-1])
//#time
