# PolCert

PolCert now exposes two user-facing entrypoints:

- [`polcert`](./POLCERT.md): the original validator-only tool for comparing two OpenScop models.
- [`polopt`](./POLOPT.md): the loop-language optimizer frontend backed by the verified optimization core.

If you only want the optimizer story, start with [`POLOPT.md`](./POLOPT.md).
If you only want the validator story, start with [`POLCERT.md`](./POLCERT.md).

## Status

- The verified optimization core now lives in [driver/PolOpt.v](./driver/PolOpt.v).
- The final optimizer definition is `Opt = Opt_prepared`.
- The final end-to-end theorem is `Opt_correct`.
- `polcert` remains the original validator CLI and is intentionally unaffected by the `polopt` work.
- The strict proved-path `polopt` regression suite currently succeeds on all generated benchmark inputs:
  - total inputs: `62`
  - succeeded: `62`
  - changed: `52`
  - unchanged: `10`

## Build

The repository is developed and tested primarily through the Docker image defined in [Dockerfile](./Dockerfile).
The recommended build order inside the container is:

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

This produces:

- `polcert <before.scop> <after.scop>`
- `polopt <file.loop>`

## CI

GitHub Actions runs the Docker-based clean build and regression flow on every push and pull request.
The CI job builds the image from [Dockerfile](./Dockerfile) and then runs [tools/ci/run_ci.sh](./tools/ci/run_ci.sh), which executes:

- the full Coq proof build
- `check-admitted`
- extraction
- `polcert` / `polopt` builds
- `make test`
- the strict `polopt` benchmark suite

## Documentation map

- [`POLCERT.md`](./POLCERT.md): validator-only executable, scope, workflow, and usage.
- [`POLOPT.md`](./POLOPT.md): verified optimizer pipeline, proof boundary, supported input language, benchmark behavior, and testing workflow.
- [`syntax/README.md`](./syntax/README.md): textual `.loop` syntax reference.
- [`tests/polopt-generated/README.md`](./tests/polopt-generated/README.md): generated strict-suite inputs and outputs.
- [`doc/`](./doc): additional design notes and analysis.

## Project structure

Main mechanized development is in:

- [`src`](./src): extractor, validator, polyhedral semantics, strengthening, prepare-codegen bridge
- [`polygen`](./polygen): verified code generation and verified cleanup passes
- [`driver`](./driver): top-level optimizer definitions and wrappers
- [`syntax`](./syntax): loop frontend used by `polopt`
- [`tests`](./tests): Pluto suite, generated `polopt` suite, scripts

## Paper

The paper of this mechanization is published at Springer:
<https://link.springer.com/chapter/10.1007/978-3-031-64626-3_17>

BibTeX:

```bibtex
@InProceedings{10.1007/978-3-031-64626-3_17,
author="Li, Xuyang
and Liang, Hongjin
and Feng, Xinyu",
editor="Chin, Wei-Ngan
and Xu, Zhiwu",
title="Verified Validation for Affine Scheduling in Polyhedral Compilation",
booktitle="Theoretical Aspects of Software Engineering",
year="2024",
publisher="Springer Nature Switzerland",
address="Cham",
pages="287--305",
isbn="978-3-031-64626-3"
}
```

## License

See [LICENSE](./LICENSE).
