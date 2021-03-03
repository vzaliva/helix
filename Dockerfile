FROM ubuntu:focal

ARG TEST_TARGET="8.12.2"

RUN apt update
RUN apt install -y opam aspcud libipc-system-simple-perl libstring-shellquote-perl

RUN opam init -n -y --compiler=4.11.1+flambda --disable-sandboxing
RUN eval $(opam config env)
RUN opam config var root

RUN opam repo add coq-released http://coq.inria.fr/opam/released || true
RUN opam install -y --verbose -j 1 coq.$TEST_TARGET && opam pin add coq $TEST_TARGET -y
RUN opam install -y --verbose -j 1 ocamlfind ocamlbuild camlp5 ${EXTRA_OPAM}
RUN opam install -y --verbose -j 1 coq-color
RUN opam install -y --verbose -j 1 coq-ext-lib
RUN opam install -y --verbose -j 1 coq-math-classes
RUN opam install -y --verbose -j 1 coq-metacoq-template
RUN opam install -y --verbose -j 1 coq-switch
RUN opam install -y --verbose -j 1 ANSITerminal
RUN opam install -y --verbose -j 1 coq-flocq
RUN opam install -y --verbose -j 1 coq-paco
RUN opam install -y --verbose -j 1 coq-ceres && opam pin add coq-ceres 0.3.0
RUN opam install -y --verbose -j 1 coq-libhyps
RUN opam install -y --verbose -j 1 menhir
RUN opam install -y --verbose -j 1 core
RUN opam install -y --verbose -j 1 core_kernel
RUN opam install -y --verbose -j 1 dune
RUN opam install -y --verbose -j 1 qcheck
RUN opam update -y
RUN opam upgrade -j 1 -y
