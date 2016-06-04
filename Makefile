LIBNAME := Spiral

.SUFFIXES:

.PHONY: default config clean clean-dep clean-all clean-doc tags doc install-doc install-dist targz graph

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\# | sed -e 's|^./||g')

default: Makefile.coq 
	$(MAKECOQ)

install-dep:
	opam instal coq coq-color coq-dpdgraph coq-math-classes coq-ext-lib

config Makefile.coq:
	coq_makefile -f _CoqProject *.v > Makefile.coq

clean:
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache`
	rm -f graph.dpd graph.dot graph.svg

clean-dep:
	rm -f `find . -name \*.v.d`

clean-all: clean
	rm -f Makefile.coq

clean-doc:
	rm -f doc/$(LIBNAME).*.html doc/index.html doc/main.html

doc:
	coqdoc --html -g -d doc -R . $(LIBNAME) *.v

graph: graph.svg

graph.svg: graph.dot
	dot -Tsvg graph.dot > graph.svg

graph.dot: graph.dpd
	dpd2dot graph.dpd

graph.dpd:
	"coqtop"  -R "." Top -I "." < depgraph.vcmd

print-unused: graph.dpd
	dpdusage -with-path graph.dpd | sort

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@
