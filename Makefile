MLCOMP=mlton
FILES=aplcompile.mlb AplCompile.sml

all: $(FILES)
	$(MLCOMP) aplcompile.mlb

test: $(FILES) test.mlb test.sml
	$(MLCOMP) test.mlb

clean:
	rm -rf *~ MLB aplcompile test