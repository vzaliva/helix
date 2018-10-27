
all: mapmain

CFLAGS = -g -O0
ASFLAGS = -g

map.s: map.ll
	llc -O=0 map.ll

map.o: map.s

mapmain: mapmain.c map.o

run: mapmain
	./mapmain

clean:
	rm -f map.s map.o mapmain
