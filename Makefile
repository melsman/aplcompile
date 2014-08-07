MLCOMP ?= mlton
FILES=aplcompile.mlb AplCompile.sml

.PHONY: all
all: aplc

aplc: $(FILES) aplc.mlb aplc.sml Makefile
	$(MLCOMP) -output aplc aplc.mlb

aplcompile: $(FILES) Makefile
	$(MLCOMP) -output aplcompile aplcompile.mlb

.PHONY: tests
tests: aplc Makefile
	$(MAKE) -C tests

.PHONY: clean
clean: Makefile
	rm -rf *~ MLB aplcompile aplc
	$(MAKE) -C tests clean 
