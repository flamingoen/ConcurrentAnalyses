path = results/result.out

default: run

all: build run

lexer:
	mono "FsLexYacc.7.0.6/build/fslex.exe" lexerParser/GuardedCommandLexer.fsl --unicode

parser:
	mono "FsLexYacc.7.0.6/build/fsyacc.exe" lexerParser/GuardedCommandParser.fsp --module GuardedCommandParser

build: lexer parser

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
