FROM ubuntu:focal

RUN apt update
RUN apt install -y opam python3-pip curl aspcud libipc-system-simple-perl libstring-shellquote-perl libgmp-dev

RUN opam init -y --bare --disable-sandboxing
RUN eval $(opam env)

RUN pip install coq-config

RUN curl -L https://raw.githubusercontent.com/vzaliva/helix/master/coq_config.yaml -o coq_config.yaml
RUN coq-config
RUN opam switch helix
