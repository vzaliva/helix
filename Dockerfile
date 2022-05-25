FROM ubuntu:focal

RUN apt update
RUN apt install -y opam curl aspcud libipc-system-simple-perl libstring-shellquote-perl libgmp-dev bison flex

RUN opam init -y --bare --disable-sandboxing
RUN eval $(opam env)

RUN opam switch create helix ocaml-base-compiler.4.12.0
RUN opam switch helix

RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam update

# A patch after [https://github.blog/2022-04-12-git-security-vulnerability-announced/]
# See also [https://community.atlassian.com/t5/Bitbucket-questions/Unsafe-repository-REPO-is-owned-by-someone-else/qaq-p/2016432]
RUN git config --global --add safe.directory '*'
