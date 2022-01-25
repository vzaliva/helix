FROM ubuntu:focal

RUN apt update
RUN apt install -y opam curl aspcud libipc-system-simple-perl libstring-shellquote-perl libgmp-dev

RUN opam init -y --bare --disable-sandboxing
RUN eval $(opam env)

RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam update

RUN opam switch create helix ocaml-base-compiler.4.12.0
RUN opam switch helix
