# Feature Status

This note is the short answer to "what is currently user-facing, what is
proved, and what interface does it use?"

## Headline compiler wrapper

The main theorem-facing optimizer wrapper is
`VerifiedParallelCompilerConfig.compile : raw_config -> Loop.t -> imp ParallelLoop.t`.
It returns `ParallelLoop.t`; sequential routes are lifted as all-sequential
annotations, and checked parallel routes preserve checked `parallel for`
annotations. The wrapper theorem is `compile_correct`, with
`compile_verified_correct` for already-accepted configs.

## `polopt`

### Default mode

Command:

```sh
./polopt file.loop
```

Status:

- theorem-aligned verified optimizer route
- affine scheduling + checked tiling
- no ISS by default

Proof object:

- optimizer: `Opt`
- theorem: `Opt_correct`

### Optional ISS mode

Command:

```sh
./polopt --iss file.loop
```

Status:

- theorem-aligned verified optimizer route
- ISS + affine scheduling + checked tiling

Proof object:

- optimizer: `Opt_with_iss`
- theorem: `Opt_with_iss_correct`

### ISS-only split checking

Command:

```sh
./polopt --iss --identity file.loop
```

Status:

- checked ISS split path
- useful for examining ISS itself without later scheduling

This route is centered on the verified ISS structural validator rather than the
default end-to-end optimizer theorem.

### Pluto-hinted checked parallel modes

Commands:

```sh
./polopt --parallel file.loop
./polopt --parallel --parallel-strict file.loop
./polopt --parallel --multipar file.loop
```

Status:

- CLI-exposed checked routes through the unified compiler wrapper
- backed by verified parallel certification and code generation components
- `--parallel-strict` requires the certified loop to match Pluto's hint
- `--multipar` uses checked multi-current configs (`RawParallelCurrentMany*`)

### Explicit-dimension parallel mode

Command:

```sh
./polopt --parallel-current 0 file.loop
```

Status:

- theorem-aligned verified optimizer route for an explicit current dimension
- supported on identity, affine-only, and full tiled paths
- also available with `--iss`

### Explicit-dimension vector mode

Command:

```sh
./polopt --vector-current 0 file.loop
```

Status:

- theorem-aligned checked vector annotation for an explicit current dimension
- reuses the parallel/doall certificate, matching Pluto's prevector source
- also exposed through Pluto compatibility as `--prevector`

Proof objects:

- `driver/ParallelPolOpt.v`
- `driver/ParallelPolOptCorrect.v`
- `Opt_parallel_current_correct`
- `Opt_parallel_current_with_iss_correct`

Relevant components:

- `src/ParallelValidator.v`
- `src/ParallelCodegen.v`
- `driver/ParallelPolOpt.v`

### Additional tiling-family selectors

Commands:

```sh
./polopt --second-level-tile file.loop
./polopt --diamond-tile file.loop
./polopt --full-diamond-tile file.loop
./polopt --legacy-generic-tiling file.loop
```

Status:

- `--second-level-tile`
  - checked second-level tiling family
  - valid on supported full tiled optimization routes and tiling
    witness/validation actions
- `--diamond-tile` / `--full-diamond-tile`
  - theorem-backed opt-in diamond phase route family
  - supported by the current route map for sequential, ISS-aware, and checked
    parallel compositions documented in `doc/pluto-polopt-compatibility.md`
  - still distinct from second-level and legacy-generic ordinary tiling
- `--legacy-generic-tiling`
  - compatibility selector for the historical generic ordinary-tiling validator
  - only supported on the default non-ISS full tiled route

### Standalone validation / inspection actions exposed by `polopt`

Commands:

```sh
./polopt --validate-affine-openscop before.scop after.scop
./polopt --extract-tiling-witness-openscop before.scop after.scop
./polopt --validate-tiling-openscop before.scop after.scop
./polopt --validate-iss-debug-dumps before.txt after.txt
./polopt --validate-iss-bridge bridge.txt
./polopt --validate-iss-pluto-suite
./polopt --validate-iss-pluto-live-suite
```

Status:

- these are validator-only / artifact-only actions, not loop-to-loop optimizer
  routes
- they cannot be mixed with route selectors or tiling-family selectors such as
  `--identity`, `--notile`, `--iss`, `--parallel`, `--parallel-strict`,
  `--diamond-tile`, `--parallel-current`, `--multipar`, `--band-tiling-experiment`, or
  `--legacy-generic-tiling`
- `--second-level-tile` is only meaningful here for tiling witness extraction
  and tiling validation

## `polcert`

### OpenScop validation modes

Commands:

```sh
./polcert before.scop after.scop
./polcert --kind tiling mid.scop after.scop
./polcert before.scop mid.scop after.scop
```

Status:

- affine validation uses OpenScop
- tiling validation uses OpenScop
- phase-aligned affine+tiling validation is supported

### ISS validation modes

Commands:

```sh
./polcert --iss-bridge bridge.txt
./polcert --iss-debug-dumps before.txt after.txt
```

Status:

- ISS is not currently validated through OpenScop
- ISS uses Pluto-derived bridge / debug-dump inputs
- this matches the fact that Pluto ISS operates on its internal program form,
  not on the old OpenScop-only path

## CI coverage

Main workflow:

- `.github/workflows/ci.yml`
- builds the repository Docker image
- runs `tools/ci/run_ci.sh`

`run_ci.sh` currently includes:

- Pluto baseline verification (`tools/ci/check_pluto_baseline.sh`)
- proof build
- `check-admitted`
- extraction
- `polcert` / `polopt` builds
- `make test`
- `make test-iss-pluto-suite`
- `make test-iss-pluto-live-suite`
- `make test-parallel-current-suite`
- `make test-vector-current-suite`
- `make test-second-level-tile-suite`
- `make test-polopt-loop-suite`

Not in default `ci` today:

- `make test-diamond-tiling-suite`
- handwritten whole-C perf harness: `tests/end-to-end-c`
- generated whole-C perf harness: `tests/end-to-end-generated`
- one-command local refresh:
  - `opam exec -- make test-end-to-end-generated-perf-refresh`

Additional workflow:

- `.github/workflows/full-tiling-suite.yml`
- runs the strict `polopt` loop suite, both ISS suites, and the
  `parallel-current` / `second-level-tile` suite targets

The strict `.loop -> .loop` gate is CI-enforced. The whole-C harnesses are
artifact-strengthening workflows and local perf campaigns, not default
correctness gates.

## Interface summary

- affine / tiling validation: OpenScop
- ISS validation: Pluto bridge / debug-dump inputs
- parallel route: `polopt` CLI only, not `polcert`
- generated whole-C perf harness:
  - wrapper-based C benchmarking, not part of the default regression gate
  - best-pipeline search currently chooses among:
    - default no-ISS affine+tiling pipeline
    - affine-only
    - ISS
    - parallel (`4` threads)
    - ISS+parallel (`4` threads)
    - identity fallback
  - the `parallel` candidates are only eligible when they emit a real verified
    `parallel for`; sequential fallbacks are not allowed to win those slots
