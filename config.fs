module Config
open Programs

// Write a program as a string or use one of the predefined programs in programs.fs
let program = goodBakery

// RD -> reaching definition
// LV -> Live variables
// DOS -> detection of signs
// DOI -> detection of intervals
// PAR -> parity
// PS -> parity + detection of signs
// DS -> parity + detection of intervals (Don't ask)
let analysisType = DOS

// Write policy as a string:
// x->odd, x->even, x->+, x->-
// x=n, x>n, x<n
// space seperated means and
// "V" seperated means or

let pol = "
c1>-1
c2>-1
"

let init = "
c1=0
c2=0
"

//let pol = "
//in2>0
//in1<0
//c1>-1
//c2>-1
//r{2}->even V r{2}<0
//"

// Analyse on a producct graph or disconected graphs
let useProduct = false

// TEST - will run analyses without output a number of times defined by testIterations
// PRINT - will run the analysis once and print the output to terminal
let mode = PRINT
let testIterations = 5

// if true - runs the analysis
let createAnalysis = true
// if true - outputs program graph to graphviz/graph.gz
let createGraph = true
// if true - outputs product graph to graphviz/productGraph.gz
let createProductGraph = true
