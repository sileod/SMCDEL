FROM ubuntu:22.04 AS build

ENV DEBIAN_FRONTEND=noninteractive
ENV PATH=/root/.local/bin:/root/.ghcup/bin:$PATH

RUN apt-get update && apt-get install -y \
    build-essential curl git libffi-dev libgmp-dev libncurses-dev libtinfo5 \
    zlib1g-dev \
    graphviz dot2tex texlive-latex-base poppler-utils preview-latex-style texlive-pstricks \
 && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org \
 | BOOTSTRAP_HASKELL_MINIMAL=1 BOOTSTRAP_HASKELL_NONINTERACTIVE=1 sh

RUN ghcup install ghc 9.4.8 \
 && ghcup set ghc 9.4.8 \
 && ghcup install stack \
 && stack config set system-ghc --global true \
 && stack config set install-ghc --global false

WORKDIR /build
COPY . .
RUN stack build --flag smcdel:web --copy-bins --local-bin-path /usr/local/bin

FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive TZ=UTC
RUN apt-get update && apt-get install -y \
    tzdata libgmp10 libffi7 libncurses5 libtinfo5 graphviz dot2tex poppler-utils zlib1g \
 && rm -rf /var/lib/apt/lists/*

COPY --from=build /usr/local/bin/smcdel /usr/local/bin/smcdel
COPY --from=build /usr/local/bin/smcdel-web /usr/local/bin/smcdel-web

WORKDIR /work
ENTRYPOINT ["smcdel"]
