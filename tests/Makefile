TESTGEN=../ml/_build/default/test.exe

.PHONY: clean test
.SECONDARY: %.s %.ll %.o

ALLTESTS=$(shell ../ml/_build/default/test.exe -p)
TESTLLS=$(addprefix test_,$(addsuffix .ll,$(ALLTESTS)))
TESTOBJS=$(addprefix test_,$(addsuffix .o,$(ALLTESTS)))

LLC=llc
LLCFLAGS=-asm-verbose -O0 -march=x86-64
ASM=gcc
ASMFLAGS=-c

test: $(TESTOBJS)

$(TESTLLS): $(TESTGEN)
	$(TESTGEN) -t $(patsubst test_%.ll, %, $@)

%.s: %.ll Makefile
	$(LLC) $(LLCFLAGS) $<

%.o: %.s Makefile
	$(ASM) $(ASMFLAGS) $<

clean:
	rm -f *.ll *.s *.o a.out
