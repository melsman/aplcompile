MLCOMP=mlton
FILES=aplcompile.mlb AplCompile.sml

.PHONY: all
all: aplc

aplc: $(FILES) aplc.mlb aplc.sml
	$(MLCOMP) aplc.mlb

aplcompile: $(FILES)
	$(MLCOMP) aplcompile.mlb

.PHONY: tests
tests: aplc
	$(MAKE) -C tests

clean:
	rm -rf *~ MLB aplcompile aplc
	$(MAKE) -C tests clean 
