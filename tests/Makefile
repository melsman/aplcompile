TESTS=test test2 test3 test4 test5 test6 test7 test9 test10 test11 test12 test13 test14 test15 test16 test19 signal test21
#TESTS=test test2 test3 test4 test5 test6 test7 test9 test10 test11 test12 test13 test14 test16 signal
TESTCOUTS=$(TESTS:%=c/%.out)
TESTOUTS=$(TESTS:%=%.out)

.PHONY: test
test: $(TESTOUTS)
#all: $(TESTCOUTS)

c/%.c: %.apl Makefile
	../aplc -c -o $@ $<
#	../aplc -o $@ $<

c/%.exe: c/%.c
	gcc --std=c99 -o $@ $<

c/%.out: c/%.exe
	$< > $@
	cat $@

%.out: %.apl Makefile
	../aplc -ml -o $@ $<
	cat $@

.PHONY: clean
clean:
	rm -f c/*.out c/*.c c/*~ *~ c/*.exe *.out
