TESTGEN=../ml/_build/default/test.exe

.PHONY: clean test
.SECONDARY: %.s %.ll %.o

ALLTESTS=$(shell ../ml/_build/default/test.exe -p)
TESTLLS=$(addprefix test_,$(addsuffix .ll,$(ALLTESTS)))
TESTOBJS=$(addprefix test_,$(addsuffix .o,$(ALLTESTS)))

LLC=llc
LLCFLAGS=-relocation-model=pic -asm-verbose -O0 -march=x86-64
ASM=gcc
ASMFLAGS=-c

test: $(TESTOBJS)

$(TESTLLS): $(TESTGEN)
	$(TESTGEN) -t $(patsubst test_%.ll, %, $@)

%.s: %.ll Makefile
	$(LLC) $(LLCFLAGS) $<

%.o: %.s Makefile
	$(ASM) $(ASMFLAGS) $<

# Individiual tests

main_pointwise_plus1: main_pointwise_plus1.c test_pointwise_plus1.o
main_pointwise_plusD: main_pointwise_plusD.c test_pointwise_plusD.o

ALLEXE=main_pointwise_plus1 main_pointwise_plusD

test: $(ALLEXE)
	$(foreach x,$(ALLEXE), echo "$(x):"; ./$(x);)

clean:
	rm -f *.ll *.s *.o a.out $(ALLEXE)
