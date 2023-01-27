FROM ubuntu:22.04

# make apt and opam noninteractive (especially important for opam depext)
RUN echo 'APT::Get::Assume-Yes "true";' > /etc/apt/apt.conf.d/90assumeyes
ARG OPAMYES=true

RUN apt-get update
RUN apt-get upgrade
RUN apt-get install opam

RUN opam init --bare --disable-sandboxing
RUN opam switch create helix ocaml-base-compiler \
    --repositories=default,coq-released=https://coq.inria.fr/opam/released

COPY ./helix.opam /tmp/helix.opam
RUN opam install --depext-only /tmp/helix.opam # system dependencies with apt
RUN opam install --deps-only /tmp/helix.opam   # project dependencies with opam

# run commands in the correct opam environment without [eval $(opam env)]
ENTRYPOINT ["opam", "exec", "--"]
