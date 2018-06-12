#r "FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll"

open System
open System.IO
type analysisType = RD | LV | DOS | DOI | PAR | PS | DS
type analysisMode = TEST | PRINT

printfn"\nLoading files"
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
#load "analyses/combinatorialAnalysis.fs"
#load "worklistAlgorithm.fs"
#load "analysis.fs"
#load "config.fs"
stopWatch.Stop()
printfn "load time:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

open ProgramGraphs
open PolicyGenerator
open TreeGenerator
open GraphViz
open Analysis
open Config

printfn"\nCompiling program"
stopWatch.Restart()
let syntaxTree = try parseProgram program with e -> failwith ("could not parse program:\n"+program)
let p = try parsePolicy pol with e -> failwith ("Could not parse policy:\n"+pol)
let (g,e) = normalizeGraph ( pgGen syntaxTree )
let (gp,ep) = productGraph g e
stopWatch.Stop()
printfn "Compile time:\t%f ms" stopWatch.Elapsed.TotalMilliseconds

if createGraph then makeGraph g e
if createProductGraph then makeProductGraph gp e

let rec test (stopWatch:System.Diagnostics.Stopwatch) times =
    if times>0 then
        stopWatch.Restart()
        RDtest g e -1
        stopWatch.Stop()
        printfn "Analysis time: %f ms" stopWatch.Elapsed.TotalMilliseconds
        test stopWatch (times-1)
    else printfn "Test finished"

if createAnalysis then
    printfn"\nCreating analysis"
    match mode with
    | PRINT ->
        match analysisType with
        | RD  when useProduct -> reachingDefinition gp ep (Set.ofList [-1])
        | RD  -> reachingDefinition g e -1
        | LV  when useProduct -> liveVariables gp ep
        | LV  -> liveVariables g e
        | DOS when useProduct -> detectionOfSignsAnalysis gp p ep
        | DOS -> detectionOfSignsAnalysis g p e
        | DOI when useProduct -> intervalAnalysis gp p ep
        | DOI -> intervalAnalysis g p e
        | PAR when useProduct -> parityAnalysis gp p ep
        | PAR -> parityAnalysis g p e
        | PS  when useProduct -> parSignAnalysis gp p ep
        | PS  -> parSignAnalysis g p e
        | DS when useProduct -> parIntAnalysis gp p ep
        | DS -> parIntAnalysis g p e
    | TEST -> test stopWatch testIterations
