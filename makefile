path = results/result.out

default: run

all: build run

lexer:
	mono "FsLexYacc.7.0.6/build/fslex.exe" lexerParser/GuardedCommandLexer.fsl --unicode

parser:
	mono "FsLexYacc.7.0.6/build/fsyacc.exe" lexerParser/GuardedCommandParser.fsp --module GuardedCommandParser

policies:
	mono "FsLexYacc.7.0.6/build/fslex.exe" lexerParser/PoliciesLexer.fsl --unicode
	mono "FsLexYacc.7.0.6/build/fsyacc.exe" lexerParser/PoliciesParser.fsp --module PoliciesParser

build: lexer parser policies

run:
	@fsharpi main.fsx

output:
	@fsharpi main.fsx > $(path)
	@cat $(path)

cleanOut:
	rm results/*
	rm graphviz/*

cleanParserLexer:
	rm lexerParser/GuardedCommandLexer.fs lexerParser/GuardedCommandParser.fs lexerParser/GuardedCommandParser.fsi

clean: cleanOut cleanParserLexer
