FROM ubuntu:focal

ARG TEST_TARGET="8.13.2"

RUN apt update
RUN apt install -y opam aspcud libipc-system-simple-perl libstring-shellquote-perl libgmp-dev

RUN opam init -n -y --compiler=4.12.0 --disable-sandboxing
RUN eval $(opam config env)

RUN opam repo add coq-released http://coq.inria.fr/opam/released || true
RUN opam update -y

RUN opam install -y --verbose -j 1 coq.$TEST_TARGET && opam pin add coq $TEST_TARGET -y
RUN opam install -y --verbose -j 1 ocamlfind ocamlbuild camlp5 ${EXTRA_OPAM}
RUN opam install -y --verbose -j 1 coq-itree
RUN opam install -y --verbose -j 1 coq-mathcomp-ssreflect
RUN opam install -y --verbose -j 1 coq-simple-io
RUN opam install -y --verbose -j 1 coq-color
RUN opam install -y --verbose -j 1 coq-ext-lib
RUN opam install -y --verbose -j 1 coq-math-classes
RUN opam install -y --verbose -j 1 coq-metacoq-template
RUN opam install -y --verbose -j 1 coq-switch
RUN opam install -y --verbose -j 1 ANSITerminal
RUN opam install -y --verbose -j 1 coq-flocq
RUN opam install -y --verbose -j 1 coq-paco
RUN opam install -y --verbose -j 1 coq-ceres
RUN opam install -y --verbose -j 1 coq-libhyps
RUN opam install -y --verbose -j 1 menhir
RUN opam install -y --verbose -j 1 core
RUN opam install -y --verbose -j 1 core_kernel
RUN opam install -y --verbose -j 1 dune
RUN opam install -y --verbose -j 1 qcheck

RUN opam update -y
RUN opam upgrade -j 1 -y
