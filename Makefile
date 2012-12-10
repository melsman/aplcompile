MLCOMP=mlton
FILES=aplcompile.mlb AplCompile.sml

all: $(FILES)
	$(MLCOMP) aplcompile.mlb

test: $(FILES) test.mlb test.sml
	$(MLCOMP) test.mlb

TESTFILES=test.apl test2.apl test3.apl test4.apl test5.apl test6.apl test7.apl test8.apl signal.apl
.PHONY: tests
tests:
	$(foreach tf,$(TESTFILES),./test tests/$(tf);)

clean:
	rm -rf *~ MLB aplcompile test