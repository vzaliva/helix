LIBNAME := Helix

.SUFFIXES:

.PHONY: default config clean clean-dep clean-ml distclean clean-doc tags doc install-doc install-dist targz graph wc print-unused extracted all run test

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

extracted: $(TSTAMP) .depend Makefile.coq

.depend: $(VFILES) 
	@echo "Analyzing Coq dependencies in" $(VFILES)
	coqdep -f _CoqProject $^ > .depend


# Exclude some proofs from list of files required to run tests
# This allows us to run unit tests even if sources just partially compile
TESTVOFILES = $(filter-out coq/DynWin/DynWinProofs.vo coq/LLVMGen/Correctness.vo, $(VOFILES))

$(TSTAMP): $(TESTVOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	rm -f $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli
	$(COQEXEC) $(EXTRACTDIR)/Extract.v
	patch -p0 < lib/CRelationClasses.mli.patch
	touch $(TSTAMP)

EXE=ml/_build/default/testeval.exe

$(CEXE): extracted ml/dune ml/extracted/dune ml/testcomp.ml
	@echo "Compiling $(CEXE)"
	(cd ml; dune build --profile=dev testcomp.exe)

$(EXE): extracted ml/dune ml/extracted/dune ml/testeval.ml
	@echo "Compiling $(EXE)"
	(cd ml; dune build --profile=dev testeval.exe)

test: $(EXE)
	ml/_build/default/testeval.exe

install-dep:
	opam instal coq coq-color coq-dpdgraph coq-math-classes coq-ext-lib

config Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean-ml:
	make -j1 -C tests clean
	rm -f $(TSTAMP) $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli 
	rm -rf _build ml/_build $(EXTRACTDIR)/_build
	rm -f *.log *.cache

clean: clean-ml
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache -o -name \*.timing`
	rm -f graph.dpd graph.dot graph.svg
	rm -f moddep.dot moddep.svg

clean-dep:
	rm -f .depend
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
	sed -ie 's/coq\///g; s/\//./g' depgraph.vcmd

graph: graph.svg

graph.svg: graph.dot
	dot -Tsvg graph.dot > graph.svg

graph.dot: graph.dpd
	dpd2dot graph.dpd

graph.dpd: depgraph.vcmd
	coqtop $(COQINCLUDES) < depgraph.vcmd

wc:
	coqwc $(MYVFILES)

print-unused: graph.dpd
	dpdusage -with-path graph.dpd | grep -v 'Memory.NM\|Memory.NP\|Memory.NE\|Memory.NS\|SigmaHCOLRewriting.NM' \
				      | grep -v 'MemoryOfCarrierA\|DSHCOLOnCarrierA\|MDSHCOLOnFloat64\|Int64asNT\|StringOT\|CarrierA_as_OT' | sort

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@

moddep.dot: Makefile
	coqdep -R . $(LIBNAME) $(MYVFILES)  -dumpgraphbox moddep.dot

moddep.svg: moddep.dot Makefile
	dot -Tsvg moddep.dot > moddep.svg

timing: .depend Makefile.coq
	$(MAKECOQ) TIMING=1

update-vellvm:
	make -C lib/vellvm/src clean
	make -C lib/vellvm/lib/InteractionTrees clean
	(cd lib/vellvm; git pull --recurse-submodules; make -C src update-trees)
	make -C lib/vellvm/src clean
	make -C lib/vellvm/lib/InteractionTrees clean
	make -C lib/vellvm/src

benchmark: timing
	find .  -name "*.v.timing" -exec awk -F " " \
		'{print $$6 "s @" $$2 "-" $$4 " " $$5 " " FILENAME}' \
		{} \; | sort -n | column -t | tail -n 50
