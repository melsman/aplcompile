MLCOMP ?= mlton
FILES=aplcompile.mlb AplCompile.sml

.PHONY: all
all: aplc

aplc: lib/github.com/melsman/MoA $(FILES) aplc.mlb aplc.sml Makefile
	$(MLCOMP) -output aplc aplc.mlb

.PHONY: install
install: aplc
	cp -p aplc $(DESTDIR)/bin/

.PHONY: test
test: aplc Makefile
	$(MAKE) -C tests test

.PHONY: clean
clean: Makefile
	rm -rf *~ MLB aplc
	$(MAKE) -C tests clean

lib/github.com/melsman/MoA:
	smlpkg sync
