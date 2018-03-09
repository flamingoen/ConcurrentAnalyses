path = results/result.out

all: run

lexer:
	mono "FsLexYacc.7.0.6/build/fslex.exe" GuardedCommandLexer.fsl --unicode

parser:
	mono "FsLexYacc.7.0.6/build/fsyacc.exe" GuardedCommandParser.fsp --module GuardedCommandParser

build: lexer parser

run:
	fsharpi main.fsx

output:
	fsharpi main.fsx > $(path)
