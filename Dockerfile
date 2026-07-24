# Keep these defaults aligned with tools/ci/pluto-baseline.env.
ARG PLUTO_IMAGE=hughshine/pluto-verif@sha256:0e15a7614af280b02ab0dc31f110c3ee3f7a1fe3ee3d1b503cc3400d87b4f4ce
ARG PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_GIT_COMMIT=488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02

FROM ${PLUTO_IMAGE} AS development-base

ARG PLUTO_IMAGE
ARG PLUTO_GIT_REMOTE
ARG PLUTO_GIT_COMMIT
ARG POLCERT_GIT_COMMIT=unknown

LABEL com.polcert.version="0.9" \
      com.polcert.pluto.image="${PLUTO_IMAGE}" \
      com.polcert.pluto.remote="${PLUTO_GIT_REMOTE}" \
      com.polcert.pluto.commit="${PLUTO_GIT_COMMIT}"

ENV PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_PLUTO_IMAGE="${PLUTO_IMAGE}" \
    POLCERT_PLUTO_GIT_REMOTE="${PLUTO_GIT_REMOTE}" \
    POLCERT_PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}"

ENV TZ=Europe/Minsk
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN  apt-get update \
  && apt-get install -y wget make m4 build-essential patch unzip git libgmp3-dev libgmp-dev libglpk-dev libeigen3-dev \
  && rm -rf /var/lib/apt/lists/*

RUN git -C /pluto fetch "${PLUTO_GIT_REMOTE}" "${PLUTO_GIT_COMMIT}" \
  && git -C /pluto checkout "${PLUTO_GIT_COMMIT}" \
  && cd /pluto \
  && ./configure --enable-glpk --with-glpk-prefix=/usr \
  && make clean \
  && make -j"$(nproc)" \
  && make install

RUN wget https://github.com/ocaml/opam/releases/download/2.0.8/opam-2.0.8-x86_64-linux --no-check-certificate -O opam && \
    echo "95365a873d9e3ae6fb48e6109b5fc5df3b4e526c9d65d20652a78e263f745a35  opam" | sha256sum -c - && \
    chmod 744 opam && \
    mv opam /usr/local/bin/opam

RUN opam init -y --verbose --disable-sandboxing --bare

RUN test -r /root/.opam/opam-init/init.sh && . /root/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true

RUN opam switch create polcert 4.13.1

RUN opam install -y \
    coq.8.13.2 \
    dune.3.22.2 \
    glpk.0.1.8 \
    menhir.20260209 \
    ocamlfind.1.9.8 \
    stdlib-shims.0.3.0 \
    zarith.1.14

RUN echo 'eval $(opam env)' >> ~/.bashrc

# prepare the server for documentation
RUN apt-get update && apt-get install -y apache2 && apt-get clean && rm -rf /var/lib/apt/lists/*
ENV APACHE_RUN_USER  www-data
ENV APACHE_RUN_GROUP www-data
ENV APACHE_LOG_DIR   /var/log/apache2
ENV APACHE_PID_FILE  /var/run/apache2/apache2.pid
ENV APACHE_RUN_DIR   /var/run/apache2
ENV APACHE_LOCK_DIR  /var/lock/apache2
ENV APACHE_LOG_DIR   /var/log/apache2
RUN mkdir -p $APACHE_RUN_DIR
RUN mkdir -p $APACHE_LOCK_DIR
RUN mkdir -p $APACHE_LOG_DIR
COPY doc/index.html /var/www/html

EXPOSE 80

# prepare the editor, here we use vim
RUN apt-get update && apt-get install -y vim cloc && apt-get clean && rm -rf /var/lib/apt/lists/*

SHELL ["/bin/bash", "-c"]

COPY . /polcert/

WORKDIR /polcert/

RUN eval $(opam env) && ./configure x86_64-linux 

LABEL org.opencontainers.image.revision="${POLCERT_GIT_COMMIT}"
ENV POLCERT_GIT_COMMIT="${POLCERT_GIT_COMMIT}"

# RUN make && make test

ENTRYPOINT /usr/sbin/apache2 && bash

FROM development-base AS artifact

ARG POLCERT_GIT_COMMIT=unknown
ARG POLCERT_RELEASE_TAG=unknown
ARG POLCERT_SOURCE_ARCHIVE_SHA256=unknown

RUN printf '%s' "${POLCERT_GIT_COMMIT}" \
      | grep -Eq '^[0-9a-f]{40}$' \
    && test -n "${POLCERT_RELEASE_TAG}" \
    && test "${POLCERT_RELEASE_TAG}" != "unknown" \
    && printf '%s' "${POLCERT_SOURCE_ARCHIVE_SHA256}" \
      | grep -Eq '^[0-9a-f]{64}$'

RUN eval $(opam env --switch=polcert) \
    && make clean \
    && make depend \
    && /usr/bin/time -v make -j1 polopt polcert.ini polcert

RUN printf '{\n  "polcert_git_commit": "%s",\n  "polcert_release_tag": "%s",\n  "polcert_source_archive_sha256": "%s",\n  "pluto_git_commit": "%s"\n}\n' \
      "${POLCERT_GIT_COMMIT}" \
      "${POLCERT_RELEASE_TAG}" \
      "${POLCERT_SOURCE_ARCHIVE_SHA256}" \
      "$(git -C /pluto rev-parse HEAD)" \
      > /polcert/BUILD_PROVENANCE.json

LABEL org.opencontainers.image.revision="${POLCERT_GIT_COMMIT}" \
      org.opencontainers.image.version="${POLCERT_RELEASE_TAG}" \
      com.polcert.source.archive-sha256="${POLCERT_SOURCE_ARCHIVE_SHA256}"

ENV POLCERT_GIT_COMMIT="${POLCERT_GIT_COMMIT}" \
    POLCERT_RELEASE_TAG="${POLCERT_RELEASE_TAG}" \
    POLCERT_SOURCE_ARCHIVE_SHA256="${POLCERT_SOURCE_ARCHIVE_SHA256}" \
    POLCERT_REQUIRE_PROVENANCE=1

FROM development-base AS development
