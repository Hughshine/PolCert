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
- tiling reports `permutable-band` when the complete direct semantic checker
  accepts the recognized layout, otherwise `rejected`
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

The no-tiling form `./polopt --iss --notile file.loop` uses the new
`RawAffineISS` sequential configuration: checked ISS, checked affine
scheduling, and verified code generation without a tiling phase.

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
- validates pairwise commutativity at the selected padded schedule coordinate,
  then connects that certificate to the actual generated loop traces
- `ParallelLoop.semantics` admits arbitrary order-preserving interleavings;
  the code-generation proof derives an ordered proof companion for each actual
  execution and uses the certificate to justify every cross-iteration move
- `--parallel-strict` requires the certified loop to match Pluto's hint
- `--multipar` submits every dimension in the finite candidate list constructed
  for that route to checked multi-current configs (`RawParallelCurrentMany*`);
  no two-element truncation remains

### Explicit-dimension parallel mode

Command:

```sh
./polopt --parallel-current 0 file.loop
```

Status:

- theorem-facing optimizer route for an explicit padded schedule coordinate;
  `current` remains in the option name for compatibility
- clean output is used when all proof-relevant cleanup stages are trace-safe;
  otherwise the route returns the checked standard-raw codegen form
- supported on identity, affine-only, and full tiled paths
- also available with `--iss`

### Explicit-dimension vector mode

Command:

```sh
./polopt --vector-current 0 file.loop
```

Status:

- theorem-aligned checked vector annotation for an explicit padded schedule coordinate
- reuses the parallel/doall certificate, matching Pluto's prevector source
- the formal `VecMode` semantics preserves sequential trace order; no SIMD
  backend execution semantics is modeled
- also exposed through Pluto compatibility as `--prevector`
- accepts only a certified innermost loop; non-innermost explicit selections
  are rejected

### Checked unroll-jam postpass

`--unrolljam` runs verified block/remainder unrolling, validates each proposed
jam, and applies verified cleanup after the selected sequential producer.
`--const-unroll` is a separate postpass that completely expands loops with
integer-constant lower and upper bounds. Sequential output applies it to every
loop. Parallel output applies the annotated version only to `SeqMode` loops,
preserving `ParMode`/`VecMode` annotations and their origin tags. The checked
composition is covered by
`extracted_parallel_compile_with_const_unroll_correct`.

`--unrolljam --parallel` is supported when the transformed Loop can be
re-extracted: PolOpt obtains a fresh parallel certificate after unroll-jam.
The constant-range regression case exercises this composition. Symbolic
`Div`/`Max`/`Min` bounds and all vector combinations are rejected at the
current boundary.

Proof objects:

- `driver/ParallelPolOpt.v`
- `src/ParallelCodegen.v`
- `checked_vector_current_annotated_codegen`
- `checked_vector_current_annotated_codegen_correct`
- `checked_vector_annotated_codegen_correct_general`

Relevant components:

- `src/ParallelValidator.v`
- `src/ParallelCodegen.v`
- `driver/ParallelPolOpt.v`

The vector route reuses the same doall certificate family as checked
parallelization, but emitted `vector for` annotations are justified by the vector
codegen correctness lemmas rather than by the ordinary parallel route theorem
alone. Pluto-hinted vector mode searches only the supplied innermost hints. It
does not search non-innermost schedule coordinates.

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
  - grouped and interleaved layouts that satisfy the direct structural gate can
    report `permutable-band`; the supported identity/mixed layouts use
    program-wide semantic reconstruction or the phase-aware direct bridge
- `--diamond-tile` / `--full-diamond-tile`
  - theorem-backed opt-in diamond phase route family
  - supported by the current route map for sequential, ISS-aware, and checked
    parallel compositions documented in `doc/pluto-polopt-compatibility.md`
  - still distinct from second-level and ordinary-tiling compatibility flags
  - their tiling leg can use the direct common-band check; the final affine leg
    is checked separately by `validate_general`
- `--legacy-generic-tiling`
  - deprecated compatibility alias for the default direct-first ordinary
    tiling dispatcher; it no longer bypasses the permutable-band check
  - only supported on the default non-ISS full tiled route

The direct checker is a semantic analogue of Pluto's fully permutable-band
condition, not Pluto's detector or band-search algorithm. It reuses the proved
access-conflict and polyhedral-emptiness kernels without calling the whole
affine-schedule validator. Ordinary rectangular, diamond, full-diamond, and
recognized second-level layouts can take the direct route. Source-like identity
layouts and structurally matched mixed-depth layouts use proved direct
program-wide schedule reconstruction or the direct strict-zero-row
normalization. Layouts outside the proved recognizers are rejected.

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
- the standalone affine action trusts the supplied OpenScop domain/access
  summaries and ignores statement bodies; it establishes schedule refinement
  under those summaries, not arbitrary OpenScop-body or C equivalence
- complete `.loop` compilation imports only the candidate scattering and keeps
  the source instruction/domain/access data, so it does not inherit that
  standalone trust boundary
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
- builds once with `tools/ci/run_ci_build.sh`
- runs isolated shards with `tools/ci/run_ci_shards.sh`

The build and shard scripts currently include:

- Pluto baseline verification (`tools/ci/check_pluto_baseline.sh`)
- proof build
- `check-admitted`
- extraction
- `polcert` / `polopt` builds
- `make test`
- legacy failure-exit contracts
- `make test-extracted-zero-fallback`
- `make test-iss-pluto-suite`
- `make test-iss-pluto-live-suite`
- `make test-parallel-current-suite`
- `make test-vector-current-suite`
- `make test-second-level-tile-suite`
- `make test-polopt-loop-suite`
- `make test-diamond-tiling-suite`
- handwritten whole-C correctness checks
- generated whole-C correctness checks over all 62 materialized cases

Not in default `ci` today:

- repeated handwritten whole-C performance runs
- generated whole-C performance search and tuning
- one-command local refresh:
  - `opam exec -- make test-end-to-end-generated-perf-refresh`

Additional workflow:

- `.github/workflows/full-tiling-suite.yml`
- runs the strict `polopt` loop suite, both ISS suites, and the
  `parallel-current` / `second-level-tile` suite targets

The strict `.loop -> .loop` effect gate and the one-repeat whole-C semantic
comparisons are CI-enforced. Repeated performance campaigns remain local
artifact workflows.

## Interface summary

- affine / tiling validation: OpenScop
- ISS validation: Pluto bridge / debug-dump inputs
- parallel route: `polopt` CLI only, not `polcert`
- generated whole-C harness:
  - one-repeat semantic comparison is part of the default regression gate
  - repeated timing and pipeline search are not part of default CI
  - best-pipeline search currently chooses among:
    - default no-ISS affine+tiling pipeline
    - affine-only
    - ISS
    - parallel (`4` threads)
    - ISS+parallel (`4` threads)
    - identity pipeline
  - the `parallel` candidates are only eligible when they emit a `parallel for`
    through the checked annotation route; sequential candidates are not allowed
    to win those slots
