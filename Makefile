LIBNAME := Helix

.SUFFIXES:

.PHONY: default config clean clean-dep distclean clean-doc tags doc install-doc install-dist targz graph wc print-unused

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VDIR := coq
LIBVFILES := $(VDIR)/Tactics/CpdtTactics.v $(VDIR)/Tactics/StructTactics.v
VFILES := $(shell find $(VDIR) -name \*.v | grep -v .\#)
MYVFILES := $(filter-out $(LIBVFILES), $(VFILES))

default: Makefile.coq 
	$(MAKECOQ)

install-dep:
	opam instal coq coq-color coq-dpdgraph coq-math-classes coq-ext-lib

config Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean:
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache`
	rm -f graph.dpd graph.dot graph.svg
	rm -f moddep.dot moddep.svg

clean-dep:
	rm -f `find . -name \*.v.d`

distclean: clean clean-dep clean-doc
	rm -f Makefile.coq Makefile.coq.conf

clean-doc:
	rm -f doc/$(LIBNAME).* doc/index.html doc/main.html coqdoc.sty coqdoc.css

doc: $(MYVFILES)
	coqdoc --html  --utf8 -d doc -R . $(LIBNAME) $(MYVFILES)
	coqdoc --latex --utf8 -d doc -R . $(LIBNAME) $(MYVFILES)

depgraph.vcmd: *.vo
	rm -f depgraph.vcmd
	echo "Require dpdgraph.dpdgraph." > depgraph.vcmd
	echo "Require $(MYVFILES:.v=)." >> depgraph.vcmd
	echo "Print FileDependGraph $(MYVFILES:.v=)." >> depgraph.vcmd

graph: graph.svg

graph.svg: graph.dot
	dot -Tsvg graph.dot > graph.svg

graph.dot: graph.dpd
	dpd2dot graph.dpd

graph.dpd: depgraph.vcmd
	coqtop  -R "." $(LIBNAME) -I "." < depgraph.vcmd

wc:
	coqwc $(MYVFILES)

print-unused: graph.dpd
	dpdusage -with-path graph.dpd | sort

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@

moddep.dot: Makefile
	coqdep -R . $(LIBNAME) $(MYVFILES)  -dumpgraphbox moddep.dot

moddep.svg: moddep.dot Makefile
	dot -Tsvg moddep.dot > moddep.svg

