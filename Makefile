.DEFAULT_GOAL := tensors

all:
	@dune build

tensors: 
	@dune build theories

examples:
	@dune build Examples

clean:
	@dune clean

install:
	@dune install

uninstall:
	@dune uninstall

# hacky :) we should replace with dune in a future version
FILES=$(shell find . -name "*.v" -depth 1) 
doc: all
	mkdir -p docs
	cd _build/default && coqdoc -g --utf8 --toc --no-lib-name -d ../../docs -R . QuantumLib $(FILES)

hooks:
	@git config core.hooksPath .hooks

.PHONY: all clean install uninstall doc
