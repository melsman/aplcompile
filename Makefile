MLCOMP=mlton
FILES=aplcompile.mlb AplCompile.sml

.PHONY: all
all: aplc

aplc: $(FILES) aplc.mlb aplc.sml
	$(MLCOMP) aplc.mlb

aplcompile: $(FILES)
	$(MLCOMP) aplcompile.mlb

TESTFILES=test.apl test2.apl test3.apl test4.apl test5.apl test6.apl test7.apl test8.apl test9.apl test10.apl test11.apl test12.apl test13.apl test14.apl signal.apl
.PHONY: tests
tests: aplc
	$(foreach tf,$(TESTFILES),./aplc tests/$(tf);)

clean:
	rm -rf *~ MLB aplcompile aplc