# PolCert

PolCert provides two user-facing tools:

- [`polcert`](./POLCERT.md): validate a Pluto/OpenScop scheduling result.
  Also supports ISS bridge / debug-dump validation modes.
- [`polopt`](./POLOPT.md): run a verified polyhedral optimization pipeline on a structured loop fragment.

If you care about the optimizer, start with [`POLOPT.md`](./POLOPT.md).
If you already have OpenScop files and only want validation, start with [`POLCERT.md`](./POLCERT.md).
For a concise note on the current verified pipeline family, see
[`doc/VERIFIED_PIPELINE.md`](./doc/VERIFIED_PIPELINE.md). For the current
feature matrix, including ISS and parallel status, see
[`doc/FEATURE_STATUS.md`](./doc/FEATURE_STATUS.md). For the user-facing flag
model and why some combinations are rejected, see
[`doc/POLOPT_FLAG_GUIDE.md`](./doc/POLOPT_FLAG_GUIDE.md).

## Environment and setup

The standard environment for this repository is defined by [Dockerfile](./Dockerfile).
If you want the supported setup, use Docker or a container built from that file.
If you prefer to configure the environment manually, treat `Dockerfile` as the source of truth and mirror its dependencies.
Detailed instructions are in [ENVIRONMENT.md](./ENVIRONMENT.md).

## Quick start

Inside the project container, build with:

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

- `./polcert <before.scop> <after.scop>`
- `./polopt <file.loop>`

For the full local regression flow, also run:

```sh
opam exec -- make test-iss-pluto-suite
opam exec -- make test-iss-pluto-live-suite
opam exec -- make test-tiling-route-suites
opam exec -- make test-polopt-loop-suite
```

If you only want to refresh the generated strict-suite corpus for downstream
whole-C harnesses, without running the strict checker gate, use:

```sh
opam exec -- make materialize-polopt-loop-suite
```

The heavier generated end-to-end perf campaign is intentionally **not** part of
default CI. Run it locally with:

```sh
opam exec -- make test-end-to-end-generated-perf-refresh
```

## Two usage stories

### 1. I already have Pluto `before.scop` / `after.scop`

Use [`polcert`](./POLCERT.md).
It checks whether the schedule change preserves the polyhedral dependence semantics.

### 2. I have a loop nest and want the optimizer to do the full pipeline

Use [`polopt`](./POLOPT.md).
By default it runs the theorem-aligned affine+tiling optimization pipeline.
It also exposes:

- an optional theorem-aligned ISS path via `--iss`
- a theorem-aligned explicit-dimension parallel path via `--parallel-current`
- a theorem-aligned innermost vector annotation path via `--vector-current`
- experimental Pluto-hinted parallel routes via `--parallel` and
  `--parallel-strict`
- experimental Pluto-hinted innermost vector annotation via `--vector` /
  `--prevector`
- experimental checked tiling-family selectors such as `--second-level-tile`,
  `--diamond-tile`, and `--full-diamond-tile`
- the deprecated ordinary-tiling compatibility alias
  `--legacy-generic-tiling`, which now uses the default band-first route
- CLI-side profiling / inspection flags such as `--profile-stages`,
  `--extract-only`, and the standalone validation actions documented in
  [`POLOPT.md`](./POLOPT.md) and
  [`doc/POLOPT_FLAG_GUIDE.md`](./doc/POLOPT_FLAG_GUIDE.md)

## Status

- The verified optimization core lives in [driver/PolOpt.v](./driver/PolOpt.v).
- The public default optimizer is `Opt_band`, proved by `Opt_band_correct`.
- The public ISS-enabled optimizer is `Opt_band_with_iss`, proved by
  `Opt_band_with_iss_correct`.
- `driver/ExtractedPipelineCorrect.v` proves the concrete extracted compiler
  configurations used by the executables.
- The explicit-dimension parallel optimizer theorems live in
  [driver/ParallelPolOptCorrect.v](./driver/ParallelPolOptCorrect.v).
- `polopt` now supports:
  - the default verified affine+tiling route
  - the optional verified ISS+affine+tiling route (`--iss`)
  - a theorem-aligned explicit-dimension parallel route (`--parallel-current`)
  - a theorem-aligned explicit-dimension innermost vector route
    (`--vector-current`)
  - experimental Pluto-hinted parallel routes (`--parallel`,
    `--parallel-strict`)
  - experimental Pluto-hinted innermost vector annotation (`--vector`,
    `--prevector`)
- `polcert` now supports:
  - direct affine validation
  - phase-aligned tiling validation
  - ISS bridge / debug-dump validation modes
- The strict proved-path `polopt` regression suite is manifest-gated in CI and
  currently succeeds on all generated benchmark inputs:
  - total inputs: `62`
  - succeeded: `62`
  - changed: `59`
  - unchanged: `3`
  - nontrivially changed: `59`
  - automatically detected tiled outputs: `39`

## CI

GitHub Actions currently has two Docker-based workflows:

- `ci`
  - clean build and regression flow on push / pull request / manual dispatch
- `full-tiling-suite`
  - stricter `polopt` loop-suite workflow on `main`, `extractor`, and pull requests

The main CI script is [tools/ci/run_ci.sh](./tools/ci/run_ci.sh). It executes:

- the full Coq proof build
- `check-admitted`
- extraction
- `polcert` / `polopt` builds
- `make test`
- `make test-iss-pluto-suite`
- `make test-iss-pluto-live-suite`
- `make test-tiling-route-suites`, which aggregates the one-level route,
  Pluto-compatibility, parallel-current, vector-current, second-level, and
  diamond suites
- the strict `polopt` benchmark suite

## Documentation map

- [`ENVIRONMENT.md`](./ENVIRONMENT.md): Docker setup, environment notes, and how to mirror the Dockerfile manually.
- [`POLCERT.md`](./POLCERT.md): validator-only executable, user workflow, and examples.
- [`POLOPT.md`](./POLOPT.md): optimizer pipeline, examples, proof boundary, benchmark behavior, and testing workflow.
- [`doc/VERIFIED_PIPELINE.md`](./doc/VERIFIED_PIPELINE.md): concise explanation of the default and optional verified pipelines, fallback behavior, and the main normalization stages.
- [`doc/FEATURE_STATUS.md`](./doc/FEATURE_STATUS.md): current user-facing mode matrix, including ISS and parallel status.
- [`doc/POLOPT_FLAG_GUIDE.md`](./doc/POLOPT_FLAG_GUIDE.md): route-family flag model, legal combinations, and why rejected combinations are rejected.
- [`doc/ARTIFACT_STRENGTHENING_PLAN.md`](./doc/ARTIFACT_STRENGTHENING_PLAN.md): next-step roadmap for whole-C benchmarking, `advect3d` codegen performance, Pluto bug studies, and diamond tiling.
- [`syntax/README.md`](./syntax/README.md): textual `.loop` syntax reference and authoring notes.
- [`tests/polopt-generated/README.md`](./tests/polopt-generated/README.md): generated strict-suite inputs, outputs, and how to inspect changes.
- [`tests/end-to-end-c/README.md`](./tests/end-to-end-c/README.md): handwritten whole-C harness cases and smoke/perf commands.
- [`tests/end-to-end-generated/README.md`](./tests/end-to-end-generated/README.md): generated whole-C perf harness, best-pipeline search, and one-command perf refresh.
- [`tests/end-to-end-generated/BEST_PIPELINES.md`](./tests/end-to-end-generated/BEST_PIPELINES.md): 62-case best-pipeline table with flags, speedups, and per-case explanations.
- [`doc/`](./doc): additional design notes and analysis.

## Project structure

Main mechanized development is in:

- [`src`](./src): extractor, validator stack, polyhedral semantics, strengthening, point-witness layer, prepare-codegen bridge
- [`polygen`](./polygen): verified code generation and verified cleanup passes
- [`driver`](./driver): top-level optimizer definitions and wrappers
- [`syntax`](./syntax): loop frontend used by `polopt`
- [`tests`](./tests): Pluto suite, generated `polopt` suite, scripts

## Paper

The paper of this mechanization is published at Springer:
<https://link.springer.com/chapter/10.1007/978-3-031-64626-3_17>

<details>
<summary>BibTeX</summary>

```bibtex
@inproceedings{li2024verified,
  title={Verified Validation for Affine Scheduling in Polyhedral Compilation},
  author={Li, Xuyang and Liang, Hongjin and Feng, Xinyu},
  booktitle={Theoretical Aspects of Software Engineering},
  pages={287--305},
  year={2024},
  publisher={Springer}
}
```

</details>

## License

See [LICENSE](./LICENSE).
