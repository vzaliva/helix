# HELIX #

HELIX: SPIRAL formalization in Coq with LLVM backend

### Dependencies ###
* [Coq 8.8.1](https://coq.inria.fr/) 
* [CoLoR](http://color.inria.fr/)
* [ExtLib](https://github.com/coq-ext-lib/coq-ext-lib)
* [math-classes](https://github.com/math-classes/math-classes)
* [Template Coq](https://template-coq.github.io/template-coq/)
* [Flocq](http://flocq.gforge.inria.fr/)
* [coq-dpdgraph](https://github.com/Karmaki/coq-dpdgraph) (optional)

To install all required dependenceis:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install --jobs=4 coq coq-color coq-ext-lib coq-math-classes coq-dpdgraph coq-template-coq coq-flocq coq-switch ANSITerminal

### Bulding and Running ###

To build:
    
    make
    
To test:

    make test

### Papers ###
* [Reification of shallow-embedded DSLs in Coq with automated verification (CoqPL 2019)](http://www.crocodile.org/lord/vzaliva-CoqPL19.pdf)
* [HELIX: A Case Study of a Formal Verification of High Performance Program Generation (FHPC 2018)](http://www.crocodile.org/lord/vzaliva-fhpc2018.pdf)
* [Formal Verification of HCOL Rewriting (FMCAD 2015)](http://www.crocodile.org/lord/Formal_Verification_of_HCOL_Rewriting_FMCAD15.pdf)

### Contact ###

[Vadim Zaliva](mailto:vzaliva@cmu.edu)

