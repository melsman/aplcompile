TESTS=test test2 test3 test4 test5 test6 test7 test9 test10 test11 test12 test13 test14 test15 test16 signal
TESTFILES=$(TESTS:%=c/%.out)

.PHONY: all
all: $(TESTFILES)

c/%.c: %.apl Makefile
	../aplc -o $@ $<

c/%.exe: c/%.c
	gcc --std=c99 -o $@ $<

c/%.out: c/%.exe
	$< > $@
	cat $@

clean:
	rm -f c/*.out c/*.c c/*~ *~