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

## CI relationship

GitHub Actions builds from [Dockerfile](./Dockerfile) and runs [tools/ci/run_ci.sh](./tools/ci/run_ci.sh).
So the Docker environment is not only a convenience; it is the canonical environment used for regression and proof validation.
