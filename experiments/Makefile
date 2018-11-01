
all: mapmain dynwinmain

CFLAGS = -O0 -no-pie
ASFLAGS = -no-pie

.SUFFIXES: .ll .s

.ll.s:
	llc -O=0 $<

map.o: map.s
dynwin.o: dynwin.s

mapmain: mapmain.c map.o

dynwinmain: dynwinmain.c dynwin.o

run: dynwinmain
	./dynwinmain

clean:
	rm -f map.s map.o mapmain dynwin.s dynwin.o dynwinmain
