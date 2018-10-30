
all: mapmain

CFLAGS = -O0 -no-pie
ASFLAGS = -no-pie

map.s: map.ll
	llc -O=0 map.ll

map.o: map.s

mapmain: mapmain.c map.o

run: mapmain
	./mapmain

clean:
	rm -f map.s map.o mapmain
