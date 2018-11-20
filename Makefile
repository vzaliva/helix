LIBNAME := Helix

.SUFFIXES:

.PHONY: default config clean clean-dep clean-ml distclean clean-doc tags doc install-doc install-dist targz graph wc print-unused extracted all

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VDIR := coq

# OCaml sources
MLDIR = ml
EXTRACTDIR = ml/extracted
TSTAMP = $(EXTRACTDIR)/.timestamp

LIBVFILES := $(VDIR)/Tactics/CpdtTactics.v $(VDIR)/Tactics/StructTactics.v
VFILES := $(shell find $(VDIR) -name \*.v | grep -v .\#)
VOFILES = $(VFILES:.v=.vo)
MYVFILES := $(filter-out $(LIBVFILES), $(VFILES))

COQINCLUDES=`grep '\-R' _CoqProject` -R $(EXTRACTDIR) Extract
COQEXEC=coqtop -q -w none $(COQINCLUDES) -batch -load-vernac-source

default: all

all: .depend Makefile.coq
	$(MAKECOQ)
	$(MAKE) extracted
	$(MAKE) $(EXE)

extracted: $(TSTAMP)

.depend: $(VFILES) 
	@echo "Analyzing Coq dependencies in" $(VFILES)
	coqdep -f _CoqProject $^ > .depend

$(TSTAMP): $(VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	patch -p0 < lib/CRelationClasses.mli.patch
	touch $(TSTAMP)

EXE=ml/_build/default/test.exe

ml/llvm_printer.ml: lib/vellvm/src/ml/llvm_printer.ml
	cp lib/vellvm/src/ml/llvm_printer.ml ml/llvm_printer.ml

ml/llvm_printer.mli: lib/vellvm/src/ml/llvm_printer.mli
	cp lib/vellvm/src/ml/llvm_printer.mli ml/llvm_printer.mli

$(EXE): extracted ml/dune ml/extracted/dune ml/llvm_printer.ml ml/llvm_printer.mli
	@echo "Compiling $(EXE)"
	(cd ml; dune build --profile=dev test.exe)

run: $(EXE)
	rm -f *.ll *.s
	./$(EXE) 

install-dep:
	opam instal coq coq-color coq-dpdgraph coq-math-classes coq-ext-lib

config Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean-ml:
	rm -f $(TSTAMP) $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli 
	rm -rf _build ml/_build $(EXTRACTDIR)/_build
	rm -f *.log *.cache
	rm -f ml/llvm_printer.ml ml/llvm_printer.mli
	rm -f *.ll

clean: clean-ml
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

depgraph.vcmd: $(VOFILES)
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

