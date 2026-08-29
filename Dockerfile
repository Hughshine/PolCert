# Keep these defaults aligned with tools/ci/pluto-baseline.env.
ARG PLUTO_IMAGE=hughshine/pluto-verif@sha256:0e15a7614af280b02ab0dc31f110c3ee3f7a1fe3ee3d1b503cc3400d87b4f4ce
ARG PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_GIT_COMMIT=8c43c210c9c08c5958198f22db4b54000380925e
ARG PLUTO_BUGGY_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_BUGGY_GIT_COMMIT=6f43860b6c4cddeeca09189bf3073f05b78b14a5
ARG PLUTO_BUGGY_ROOT=/opt/polcert/pluto-buggy

FROM ${PLUTO_IMAGE} AS buggy-pluto-builder

ARG PLUTO_BUGGY_GIT_REMOTE
ARG PLUTO_BUGGY_GIT_COMMIT

RUN apt-get update \
  && apt-get install -y libglpk-dev \
  && rm -rf /var/lib/apt/lists/* \
  && git -C /pluto remote set-url origin "${PLUTO_BUGGY_GIT_REMOTE}" \
  && git -C /pluto fetch origin "${PLUTO_BUGGY_GIT_COMMIT}" \
  && git -C /pluto checkout "${PLUTO_BUGGY_GIT_COMMIT}" \
  && cd /pluto \
  && ./configure --enable-glpk --with-glpk-prefix=/usr \
  && make clean \
  && make -j"$(nproc)"

# Export a clean checkout plus only the runtime artifacts.  Copying the build
# tree would retain hundreds of megabytes of object files in the final image.
RUN git clone --no-hardlinks /pluto /polcert-pluto-buggy \
  && git -C /polcert-pluto-buggy remote set-url origin "${PLUTO_BUGGY_GIT_REMOTE}" \
  && cp /pluto/tool/pluto /polcert-pluto-buggy/tool/pluto \
  && cp /pluto/polycc /polcert-pluto-buggy/polycc \
  && cp /pluto/inscop /polcert-pluto-buggy/inscop

FROM ${PLUTO_IMAGE} AS development-base

ENV TZ=Europe/Minsk
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN  apt-get update \
  && apt-get install -y wget make m4 build-essential patch unzip git libgmp3-dev libgmp-dev libglpk-dev libeigen3-dev \
  && rm -rf /var/lib/apt/lists/*

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
ENV APACHE_RUN_USER=www-data
ENV APACHE_RUN_GROUP=www-data
ENV APACHE_LOG_DIR=/var/log/apache2
ENV APACHE_PID_FILE=/var/run/apache2/apache2.pid
ENV APACHE_RUN_DIR=/var/run/apache2
ENV APACHE_LOCK_DIR=/var/lock/apache2
RUN mkdir -p $APACHE_RUN_DIR
RUN mkdir -p $APACHE_LOCK_DIR
RUN mkdir -p $APACHE_LOG_DIR

EXPOSE 80

# prepare the editor, here we use vim
RUN apt-get update && apt-get install -y vim cloc && apt-get clean && rm -rf /var/lib/apt/lists/*

# Keep the expensive, stable system and Rocq toolchain layers independent of
# the pinned Pluto revision. Feature branches can then reuse the main-branch
# BuildKit cache when only the candidate generator commit changes.
ARG PLUTO_GIT_REMOTE
ARG PLUTO_GIT_COMMIT

RUN git -C /pluto remote set-url origin "${PLUTO_GIT_REMOTE}" \
  && git -C /pluto fetch origin "${PLUTO_GIT_COMMIT}" \
  && git -C /pluto checkout "${PLUTO_GIT_COMMIT}" \
  && cd /pluto \
  && ./configure --enable-glpk --with-glpk-prefix=/usr \
  && make clean \
  && make -j"$(nproc)" \
  && make install

# BuildKit can compile this historical bug-reproduction baseline in parallel
# with the main image. It is never used by ordinary PolOpt routes.
ARG PLUTO_IMAGE
ARG PLUTO_BUGGY_GIT_REMOTE
ARG PLUTO_BUGGY_GIT_COMMIT
ARG PLUTO_BUGGY_ROOT

COPY --from=buggy-pluto-builder /polcert-pluto-buggy ${PLUTO_BUGGY_ROOT}
RUN sed -i "s|^pluto=/pluto|pluto=${PLUTO_BUGGY_ROOT}|" "${PLUTO_BUGGY_ROOT}/polycc" \
  && sed -i "s|^inscop=/pluto|inscop=${PLUTO_BUGGY_ROOT}|" "${PLUTO_BUGGY_ROOT}/polycc"

LABEL com.polcert.version="0.9" \
      com.polcert.pluto.image="${PLUTO_IMAGE}" \
      com.polcert.pluto.remote="${PLUTO_GIT_REMOTE}" \
      com.polcert.pluto.commit="${PLUTO_GIT_COMMIT}" \
      com.polcert.pluto.buggy-remote="${PLUTO_BUGGY_GIT_REMOTE}" \
      com.polcert.pluto.buggy-commit="${PLUTO_BUGGY_GIT_COMMIT}"

ENV PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_PLUTO_IMAGE="${PLUTO_IMAGE}" \
    POLCERT_PLUTO_GIT_REMOTE="${PLUTO_GIT_REMOTE}" \
    POLCERT_PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_BUGGY_PLUTO_GIT_REMOTE="${PLUTO_BUGGY_GIT_REMOTE}" \
    POLCERT_BUGGY_PLUTO_GIT_COMMIT="${PLUTO_BUGGY_GIT_COMMIT}" \
    POLCERT_BUGGY_ROOT="${PLUTO_BUGGY_ROOT}" \
    POLCERT_BUGGY_PLUTO="${PLUTO_BUGGY_ROOT}/tool/pluto" \
    POLCERT_BUGGY_POLYCC="${PLUTO_BUGGY_ROOT}/polycc"

COPY doc/index.html /var/www/html

SHELL ["/bin/bash", "-c"]

COPY . /polcert/

WORKDIR /polcert/

RUN eval $(opam env) && ./configure x86_64-linux 

ARG POLCERT_GIT_COMMIT=unknown
LABEL org.opencontainers.image.revision="${POLCERT_GIT_COMMIT}"
ENV POLCERT_GIT_COMMIT="${POLCERT_GIT_COMMIT}"

# RUN make && make test

ENTRYPOINT /usr/sbin/apache2 && bash

FROM development-base AS ci

ARG CI_MAX_PROOF_JOBS=2
ARG CI_PROOF_MEMORY_MB_PER_JOB=6144
ARG CI_MAX_BUILD_JOBS=4
ARG CI_BUILD_MEMORY_MB_PER_JOB=1536

ENV CI_MAX_PROOF_JOBS="${CI_MAX_PROOF_JOBS}" \
    CI_PROOF_MEMORY_MB_PER_JOB="${CI_PROOF_MEMORY_MB_PER_JOB}" \
    CI_MAX_BUILD_JOBS="${CI_MAX_BUILD_JOBS}" \
    CI_BUILD_MEMORY_MB_PER_JOB="${CI_BUILD_MEMORY_MB_PER_JOB}"

RUN bash /polcert/tools/ci/run_ci_build.sh

FROM ci AS artifact

ARG POLCERT_GIT_COMMIT=unknown
ARG POLCERT_RELEASE_TAG=unknown
ARG POLCERT_SOURCE_ARCHIVE_SHA256=unknown

RUN printf '%s' "${POLCERT_GIT_COMMIT}" \
      | grep -Eq '^[0-9a-f]{40}$' \
    && test -n "${POLCERT_RELEASE_TAG}" \
    && test "${POLCERT_RELEASE_TAG}" != "unknown" \
    && printf '%s' "${POLCERT_SOURCE_ARCHIVE_SHA256}" \
      | grep -Eq '^[0-9a-f]{64}$'

RUN printf '{\n  "polcert_git_commit": "%s",\n  "polcert_release_tag": "%s",\n  "polcert_source_archive_sha256": "%s",\n  "pluto_git_commit": "%s",\n  "pluto_buggy_git_commit": "%s"\n}\n' \
      "${POLCERT_GIT_COMMIT}" \
      "${POLCERT_RELEASE_TAG}" \
      "${POLCERT_SOURCE_ARCHIVE_SHA256}" \
      "$(git -C /pluto rev-parse HEAD)" \
      "$(git -C "$POLCERT_BUGGY_ROOT" rev-parse HEAD)" \
      > /polcert/BUILD_PROVENANCE.json

LABEL org.opencontainers.image.revision="${POLCERT_GIT_COMMIT}" \
      org.opencontainers.image.version="${POLCERT_RELEASE_TAG}" \
      com.polcert.source.archive-sha256="${POLCERT_SOURCE_ARCHIVE_SHA256}"

ENV POLCERT_GIT_COMMIT="${POLCERT_GIT_COMMIT}" \
    POLCERT_RELEASE_TAG="${POLCERT_RELEASE_TAG}" \
    POLCERT_SOURCE_ARCHIVE_SHA256="${POLCERT_SOURCE_ARCHIVE_SHA256}" \
    POLCERT_REQUIRE_PROVENANCE=1

FROM development-base AS development
