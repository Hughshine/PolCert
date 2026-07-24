# Environment setup

The recommended environment for this repository is the one described by [Dockerfile](./Dockerfile).
That file is also what GitHub CI uses, so if you want the same behavior locally, start there.

## Recommended: use Docker

Build the image:

```sh
docker build -t polcert-dev .
```

Run an interactive shell in the repository:

```sh
docker run --rm -it   -v "$PWD":/polcert   -w /polcert   polcert-dev bash
```

Inside that shell, build with the standard sequence:

```sh
make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
make test
```

## Alternative: configure manually

Manual setup is possible, but the repository does not treat handwritten setup instructions as the source of truth.
If you go this route, mirror the toolchain and dependencies from [Dockerfile](./Dockerfile).

In practice, that means:

- use the same base OS assumptions as the Docker image
- install the same OCaml / opam / Coq / Menhir / build dependencies
- install the same Pluto / OpenScop-related tools expected by the tests
- build and run the project with the same command sequence used in Docker and CI

If a manual environment behaves differently from Docker, Docker should be treated as the reference.

## Reproducible release artifact

The `artifact` Docker target compiles PolCert inside the image and requires
source provenance at build time. Build it from a clean, tagged checkout:

```sh
COMMIT=$(git rev-parse HEAD)
RELEASE_TAG=$(git describe --tags --exact-match "$COMMIT")
SOURCE_ARCHIVE=/tmp/polcert-"$COMMIT".tar
git archive --format=tar --output="$SOURCE_ARCHIVE" "$COMMIT"
SOURCE_SHA256=$(sha256sum "$SOURCE_ARCHIVE" | cut -d ' ' -f 1)
IMAGE=polcert-artifact:"$RELEASE_TAG"

docker build --target artifact \
  --build-arg POLCERT_GIT_COMMIT="$COMMIT" \
  --build-arg POLCERT_RELEASE_TAG="$RELEASE_TAG" \
  --build-arg POLCERT_SOURCE_ARCHIVE_SHA256="$SOURCE_SHA256" \
  -t "$IMAGE" - < "$SOURCE_ARCHIVE"
```

Run the full claim suite without mounting the source tree:

```sh
IMAGE_DIGEST=$(docker image inspect "$IMAGE" --format '{{.Id}}')
test -n "$IMAGE_DIGEST"

docker run --name polcert-artifact-check \
  -e POLCERT_IMAGE_DIGEST="$IMAGE_DIGEST" \
  --entrypoint bash "$IMAGE" -lc \
  'eval "$(opam env --switch=polcert)" &&
   python3 tools/artifact/run_artifact_check.py --mode full \
     --output-root /tmp/polcert-artifact-check'

docker cp \
  polcert-artifact-check:/tmp/polcert-artifact-check/artifact-results.json \
  ./artifact-results.json
```

The same tagged archive supplies both the recorded source hash and the Docker
build context, so dirty or untracked worktree files cannot enter the release
image. The runner checks the image's `BUILD_PROVENANCE.json` against the
runtime PolCert and Pluto revisions. Release-mode checks also require the
externally observed image ID (or, after publication, its registry digest),
which is recorded in `artifact-results.json`.

## CI relationship

GitHub Actions builds from [Dockerfile](./Dockerfile) and runs [tools/ci/run_ci.sh](./tools/ci/run_ci.sh).
So the Docker environment is not only a convenience; it is the canonical environment used for regression and proof validation.
