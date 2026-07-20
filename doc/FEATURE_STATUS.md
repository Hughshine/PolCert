# Feature Status

This note is the short answer to "what is currently user-facing, what is
proved, and what interface does it use?"

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

- optimizer: `Opt_band`
- route theorem: `Opt_band_correct`
- extracted dispatcher theorem: `extracted_sequential_compile_correct`

### Optional ISS mode

Command:

```sh
./polopt --iss file.loop
```

Status:

- theorem-aligned verified optimizer route
- ISS + affine scheduling + checked tiling

Proof object:

- optimizer: `Opt_band_with_iss`
- route theorem: `Opt_band_with_iss_correct`
- extracted dispatcher theorem: `extracted_sequential_compile_correct`

Bare sequential `--iss --identity` and `--iss --notile` are rejected because
the extracted sequential dispatcher has no such configuration. Identity
tiling with ISS is supported with `--identity --tile`; ISS identity/affine
forms are also available when followed by a checked parallel or vector
consumer.

### Experimental parallel modes

Commands:

```sh
./polopt --parallel file.loop
./polopt --parallel --parallel-strict file.loop
```

Status:

- CLI-exposed
- backed by verified parallel certification / code generation components
- still experimental
- not the default theorem-aligned optimizer path

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

- theorem-aligned checked innermost vector annotation for an explicit current
  dimension
- reuses the parallel/doall certificate and additionally rejects every output
  with a non-innermost vector loop or no vector loop
- the separate `--prevector` / `--vector` route consumes only Pluto's mapped
  hint and skips the optional annotation when that hint is missing or rejected

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
  - valid on ordinary full-tiled and identity-tiled routes, their checked
    consumers, and tiling witness/validation actions
- `--diamond-tile` / `--full-diamond-tile`
  - theorem-backed opt-in diamond route family
  - composes with second-level tiling, ISS, and checked parallel/vector
    consumers on the covered routes
- `--legacy-generic-tiling`
  - deprecated compatibility alias
  - no longer selects a generic-primary path; it uses the same band-first
    ordinary route as the default

Every tiling-bearing route first tries the ordinary common-band checker,
whole-program ordinary-tiling permutability, and the hierarchical second-level
checker. A structurally recognized source-like class of second-level schedules
also has a guarded whole-program permutability mode, selected by an exact
zero-row-erasure comparison between the parsed recipe roots and source
schedule. Current identity producers exercise this class; the selector does
not inspect CLI flags. The proved canonical and general
fallback validators run only after these checks fail. The external
`permutable-band` label covers all four specialized modes. Every
completed tiling attempt prints exactly one
`[tiling-validation] route=...` line: `permutable-band`, `general-fallback`, or
`rejected` when the final tiling-bearing pipeline is not adopted. A validator
rejection retains the already-validated affine midpoint. A mandatory parallel
consumer may reject the complete pipeline and report its conservative fallback.
Automatic vector annotation is optional: a missing or rejected hint retains the
verified producer and reports `status=skipped` without an alarm. Explicit
`--vector-current` is a hard assertion; rejection reports only vector telemetry,
does not emit a tiling route, and produces no optimized fallback. The
`general-fallback` label intentionally aggregates the canonical and general
proved fallback validators. The
second-level regression suite covers ordinary, identity-tiled, diamond,
full-diamond, ISS, parallel, vector, multipar, explicit-current, and strict
combinations, including explicit general-fallback cases.

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
  `--diamond-tile`, `--parallel-current`, `--band-tiling-experiment`, or
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
./polcert before.scop mid.scop posttile.scop after.scop
./polcert --second-level-tile --kind tiling mid.scop after.scop
```

Status:

- affine validation uses OpenScop
- tiling validation uses OpenScop
- phase-aligned affine+tiling validation is supported
- four-input affine/tiling/final-affine validation is supported for diamond
  phase dumps
- second-level tiling uses the same permutable-band-first dispatcher and
  reports its adopted route

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
- `make test-tiling-route-suites`, which aggregates one-level route discipline,
  Pluto compatibility, parallel-current, vector-current, second-level tiling,
  and diamond tiling
- `make test-polopt-loop-suite`

Not in default `ci` today:

- handwritten whole-C perf harness: `tests/end-to-end-c`
- generated whole-C perf harness: `tests/end-to-end-generated`
- one-command local refresh:
  - `opam exec -- make test-end-to-end-generated-perf-refresh`

Additional workflow:

- `.github/workflows/full-tiling-suite.yml`
- runs the strict `polopt` loop suite, both ISS suites, and the aggregate
  tiling-route suite

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
