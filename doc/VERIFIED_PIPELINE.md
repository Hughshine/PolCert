# Verified Pipeline

This note records the current verified `polopt` / `polcert` pipeline shape at a
high level. It is intentionally short and only explains the stages that tend to
be confusing after the tiling extension.

## Main idea

The repository now has:

- a default theorem-aligned affine+tiling optimizer route
- an optional theorem-aligned ISS+affine+tiling optimizer route
- theorem-aligned explicit-dimension parallel routes
- experimental Pluto-hinted parallel routes layered on top of those optimizer paths

The default no-ISS route remains the stable baseline. The tiling route is used
when the external two-phase Pluto pipeline succeeds and its outputs can be
imported and checked. The ISS route is separate and opt-in.

## `polopt`

There are two theorem-aligned optimizer modes:

- default: `./polopt file.loop`
- ISS-enabled: `./polopt --iss file.loop`

There is one theorem-aligned parallel family:

- `./polopt --parallel-current d ...`

And there are experimental CLI-only parallel extensions:

- `./polopt --parallel ...`
- `./polopt --parallel-strict ...`

The default optimizer pipeline is:

```text
.loop
-> extract
-> strengthen
-> checked affine schedule
-> optional checked tiling phase
-> current_view_pprog
-> prepare_codegen
-> codegen
-> cleanup
```

The main stages are:

- `Extractor.extractor`
  Builds the internal polyhedral model from the structured loop fragment.
- `StrengthenDomain.strengthen_pprog`
  Makes implicit parameter/domain facts explicit so later validation and code
  generation operate on a more precise representation.
- checked affine schedule
  Runs Pluto's affine scheduling result and validates it with the verified
  affine validator.
- optional checked tiling phase
  Runs the phase-aligned tiling route. The dispatcher first tries the ordinary
  common-band check, then whole-program ordinary-tiling permutability over the
  composed tiling semantics, and then the hierarchical second-level checker.
  Only after those specialized modes fail does it try the proved canonical and
  general fallback validators.
  Ordinary, second-level, identity-tiled, diamond, ISS, parallel, vector, and
  multipar CLI paths all share this order.
- `current_view_pprog`
  Materializes the witness-centered program as an explicit current-space affine
  view so the existing affine codegen story can be reused without teaching the
  full code generator about every witness form.
- `prepare_codegen`
  Normalizes matrix shapes and tail dimensions into the regular form expected by
  code generation. This is a formatting and regularization pass, not another
  optimization pass.
- `CodeGen.codegen`
  Produces loop code from the validated polyhedral program.
- cleanup
  Removes singleton loops and performs small structural cleanups on the
  generated loop tree.

The specialized tiling-permutability-first guarantee is an entrypoint property
of the verified compiler configurations used by `polopt` and `polcert`.
The external `permutable-band` route label covers the ordinary common-band,
ordinary whole-program, and hierarchical second-level modes. Canonical and
general validator functions remain extracted as lower-level proof components
because the unified dispatcher calls them; they are not alternative compiler
route selectors.

For every completed tiling attempt, `polopt` reports exactly one final route on
stderr: `permutable-band`, `general-fallback`, or `rejected`. The fallback
label aggregates the proved canonical and general validators; it never denotes
an unchecked compiler fallback. `rejected` means the final tiling-bearing
pipeline was not adopted. This can happen because all five tiling validation
layers rejected the candidate, in which case the already-validated affine
midpoint is retained, or because a mandatory parallel consumer rejected the
validated tiled candidate. Automatic vector annotation is instead optional:
an unusable hint reports `status=skipped` and retains the verified producer.
Explicit `--vector-current` rejection is a hard failure that reports vector
telemetry, no tiling route, and no optimized fallback.

The ISS-enabled pipeline has the same later stages, but inserts a checked ISS
structural-validation stage before later scheduling / tiling:

```text
.loop
-> extract
-> strengthen
-> checked ISS structural validation
-> checked affine schedule with ISS enabled
-> optional checked tiling phase
-> current_view_pprog
-> prepare_codegen
-> codegen
-> cleanup
```

In theorem terms, the public routes are `Opt_band_correct` and
`Opt_band_with_iss_correct`. `ExtractedPipelineCorrect.v` proves the concrete
extracted sequential and parallel compiler configurations branch by branch.

Current strict-suite snapshot:

- total generated inputs: `62`
- successful runs: `62`
- changed outputs: `59`
- nontrivially changed outputs: `59`
- automatically detected tiled outputs: `39`

Representative visible outcomes:

- `covcol` remains the standard affine-scheduling example
- `matmul-init` is now a compact explicit tiling example with extra tile loops,
  `max/min` strip-mined bounds, and visible `/ 32` tile-size arithmetic
- the dedicated ISS suites use Pluto periodic/reversal examples through the
  bridge/debug-dump validation path

Parallel status:

- verified parallel certification / code generation components exist
- the explicit-dimension route `--parallel-current d` is theorem-aligned and
  has dedicated correctness theorems in `ParallelPolOptCorrect.v`
- the Pluto-hinted routes `--parallel` / `--parallel-strict` are still
  experimental CLI routes

Performance-harness status:

- the strict 62-case `.loop -> optimized .loop` suite remains the default
  regression gate
- a heavier wrapper-based generated whole-C perf harness now exists under
  `tests/end-to-end-generated`
- it is intentionally not part of default CI
- the local refresh command is:
  - `opam exec -- make test-end-to-end-generated-perf-refresh`
- that harness currently tracks a per-case best pipeline among:
  - default no-ISS affine+tiling
  - affine-only
  - ISS
  - parallel (`4` threads)
  - ISS+parallel (`4` threads)
  - identity fallback

## `polcert`

`polcert` now exposes five practically important validation modes:

- direct affine validation of `before.scop -> after.scop`
- tiling-only validation of `mid.scop -> after.scop` with `--kind tiling`
- phase-aligned validation of `before -> mid -> after`
- four-input validation of `before -> mid -> posttile -> after`, including the
  final affine phase used by diamond pipelines
- ISS validation through `--iss-bridge` / `--iss-debug-dumps`

Tiling-only, three-input, and four-input modes accept `--second-level-tile` and
report whether the permutable-band layer or the proved fallback was adopted.

The phase-aligned route checks:

1. `before -> mid` with the affine validator
2. `mid -> after` with the checked tiling validator

The four-input route checks the same first two boundaries and then validates
`posttile -> after` with the affine validator.

The ISS route is separate:

- it validates Pluto ISS bridge / dump inputs
- it does not currently use OpenScop as its external interface

## Why there are several normalization stages

The tiling extension introduced a point-space witness layer. That means a
program can carry both:

- its current iteration-space coordinates
- the source/base coordinates used by instruction semantics

Because of that, the pipeline needs several distinct "format-fixing" stages:

- strengthening
  Improves domain precision before any external scheduling step.
- canonical tiling import
  Rebuilds the imported tiled program into the canonical internal form expected
  by the permutable-band, canonical, and general tiling validators.
- `current_view_pprog`
  Eliminates witness indirection by materializing explicit current-space
  transformations.
- `prepare_codegen`
  Regularizes the program for code generation.

These stages are not duplicates; they solve different representation problems.

The ISS extension introduces another structural layer:

- statement/domain partition refinement
- cut families and piece witnesses
- a dedicated structural validator before later schedule/codegen phases

## Proof boundary

The proved core includes:

- extraction into the internal polyhedral model
- affine validation
- checked tiling validation
- checked ISS structural validation
- current-view conversion
- prepare-codegen
- code generation
- cleanup

There are also proved parallel certification / code generation components, but
they are currently documented as experimental CLI routes rather than the stable
default theorem path.

The unproved parts remain:

- Pluto itself
- OpenScop parsing and printing details
- witness inference from external phase outputs
- frontend parsing of `.loop` text
