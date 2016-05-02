LIBNAME := Spiral

.SUFFIXES:

.PHONY: default config clean clean-dep clean-all clean-doc tags doc install-doc install-dist targz

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\# | sed -e 's|^./||g')

default: Makefile.coq
	$(MAKECOQ)

config Makefile.coq:
	coq_makefile -f _CoqProject *.v > Makefile.coq

clean:
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache`

clean-dep:
	rm -f `find . -name \*.v.d`

clean-all: clean
	rm -f Makefile.coq _CoqProject

clean-doc:
	rm -f doc/$(LIBNAME).*.html doc/index.html doc/main.html

doc:
	coqdoc --html -g -d doc -R . $(LIBNAME) *.v

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@
