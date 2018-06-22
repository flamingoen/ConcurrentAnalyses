path = results/result.out
dllPath = dlls/

default: run

all: build dll run

guardedCommands:
	@mono "FsLexYacc.7.0.6/build/fslex.exe" lexerParser/GuardedCommandLexer.fsl --unicode
	@mono "FsLexYacc.7.0.6/build/fsyacc.exe" lexerParser/GuardedCommandParser.fsp --module GuardedCommandParser

policies:
	@mono "FsLexYacc.7.0.6/build/fslex.exe" lexerParser/PoliciesLexer.fsl --unicode
	@mono "FsLexYacc.7.0.6/build/fsyacc.exe" lexerParser/PoliciesParser.fsp --module PoliciesParser

defines.dll:
	@fsharpc --target:library -o:$(dllPath)/defines.dll defines.fs

LexerParser.dll: defines.dll guardedCommands policies
	fsharpc --target:library -o:$(dllPath)/LexerParser.dll --reference:dlls/defines.dll --lib:dlls --reference:FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll lexerParser/GuardedCommandParser.fs lexerParser/PoliciesParser.fs lexerParser/PoliciesLexer.fs lexerParser/GuardedCommandLexer.fs

compiler.dll: LexerParser.dll defines.dll
	fsharpc --target:library -o:$(dllPath)/compiler.dll --reference:dlls/defines.dll --reference:FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll --reference:$(dllPath)/LexerParser.dll compiler/*

dll: LexerParser.dll compiler.dll

latexGraph:
	@dot2tex -ftikz graphviz/graph.gv


build: guardedCommands policies

run:
	@fsharpi main.fsx

output:
	@fsharpi main.fsx > $(path)
	@cat $(path)

cleanOut:
	@rm results/*
	@rm graphviz/*.gv

cleanParserLexer:
	@rm lexerParser/GuardedCommandLexer.fs lexerParser/GuardedCommandParser.fs lexerParser/GuardedCommandParser.fsi

cleanDlls:
	@rm dlls/*

clean: cleanOut cleanParserLexer cleanDlls
