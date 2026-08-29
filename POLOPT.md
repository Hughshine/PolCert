# polopt

`polopt` is the loop-language optimizer frontend backed by the verified optimization core.
It is the closest thing in this repository to a Pluto counterpart: Pluto is still used as the untrusted scheduler, but extraction, schedule validation, schedule/domain strengthening, code generation, and post-codegen cleanup are all tied to Coq proofs.

## What it does

`polopt` takes a structured loop fragment, runs the verified polyhedral
optimization core, and prints an optimized loop. The scheduler is Pluto itself,
so the optimization decisions come from Pluto; the difference is that
extraction, validation, code generation, and cleanup are integrated into proved
pipelines.

There are four practically important theorem-facing `polopt` families:

- checked affine+tiling routes, including the default sequential route
- checked ISS+affine+tiling routes (`--iss`)
- checked explicit schedule-coordinate parallel routes (the legacy-named
  `--parallel-current` option)
- checked Pluto-hinted parallel routes (`--parallel`, `--parallel-strict`, and
  `--parallel --multipar`)

The actual public CLI surface is slightly richer than that four-family summary.
In the normalized flag model, a user-visible run is built from:

- a base route:
  - default full tiled
  - `--notile`
  - `--identity`
- an optional structural extension:
  - plain
  - `--iss`
- an optional tiling-family selector on full tiled routes:
  - default band-aware ordinary tiling
  - `--band-tiling-experiment` (compatibility alias for the default band-aware
    ordinary tiling route)
  - `--legacy-generic-tiling` (deprecated compatibility alias for that same
    direct-first route)
  - `--second-level-tile`
  - `--diamond-tile`
  - `--full-diamond-tile`
- an optional parallel-family selector:
  - sequential
  - `--parallel`
  - `--parallel --parallel-strict`
  - `--parallel --multipar`
  - `--parallel-current d`

The detailed legality / rejection matrix lives in
[doc/POLOPT_FLAG_GUIDE.md](./doc/POLOPT_FLAG_GUIDE.md).

At a high level, the default pipeline is:

```text
.loop text
-> parser / elaborator
-> Loop IR
-> Extractor.extractor
-> StrengthenDomain.strengthen_pprog
-> affine Pluto route with verified affine validation
-> import the phase-aligned tiling candidate and witness
-> run the complete direct semantic permutable-band checker
   -> report permutable-band if a proved layout bridge and band check succeed
   -> otherwise report rejected
-> if tiling validation succeeds:
   -> current_view_pprog
-> otherwise:
   -> retain the verified affine midpoint
-> PrepareCodegen.prepare_codegen
-> CodeGen.codegen
-> verified cleanup passes
-> Loop IR
```

For a concise summary of the current verified pipeline shape and the role of
`current_view_pprog`, see:

- [doc/VERIFIED_PIPELINE.md](./doc/VERIFIED_PIPELINE.md)
- [doc/FEATURE_STATUS.md](./doc/FEATURE_STATUS.md)
- [doc/POLOPT_FLAG_GUIDE.md](./doc/POLOPT_FLAG_GUIDE.md)
- [doc/TILING_VALIDATION_DIRECT_STATUS.md](./doc/TILING_VALIDATION_DIRECT_STATUS.md)
- [doc/PERMUTABLE_BAND_THEORY_EXPLORATION.md](./doc/PERMUTABLE_BAND_THEORY_EXPLORATION.md)

The direct checker validates a semantic counterpart of Pluto's fully
permutable-band property for recognized tiling layouts. It checks that no
source-ordered conflicting pair with the same prefix before the band decreases
in any selected band component. It reuses the certified access-conflict and
polyhedral-emptiness kernels, but does not invoke the whole affine-schedule
validator. The check is sound for the recognized layouts; it is not a
formalization of Pluto's detector, independent-hyperplane search, or
profitability heuristics. An impure solver alarm propagates and aborts this
route; it is not converted into a fallback attempt.

Ordinary rectangular tiling and the tiling leg of diamond/full-diamond routes
can use the common-band direct check. Recognized grouped or interleaved
second-level schedules use a componentwise direct check. Program-wide semantic
schedule reconstruction covers recognized identity and mixed-depth layouts; a
phase-aware bridge covers the recognized mixed second-level shape. Layouts
outside these proved recognizers are rejected rather than sent to another
tiling validator. The
diamond route has a separate final affine leg after tiling; that leg is checked
by `validate_general` even when the tiling leg reported `permutable-band`.
`--intratileopt` uses the same proved affine, tiling, affine composition for
rectangular tiling: Pluto's tile-internal loop reordering is the final affine
leg, not part of the permutable-band judgment.

## Pluto configuration used by `polopt`

`polopt` uses phase-aligned Pluto recipes while preserving Pluto's default of
not computing read-after-read relations:

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
      --smartfuse --nounrolljam --noparallel --notile
```

This matters because the default verified path is aimed at **checked
schedule/domain transformation and schedule-driven code generation**, not at
the full Pluto transformation space. In particular, the default `polopt` path
should be read as supporting the optimization capability that Pluto exposes
**under this phase-isolated flag set**. Users can add `--rar` explicitly as an
oracle scheduling policy; it changes only the candidate and never bypasses
validation:

- affine scheduling / loop reordering
- skewing / wavefront-style rescheduling
- statement reordering, fission, and related schedule effects
- schedule changes that stay within the validated affine-scheduling story

See [the Pluto RAR policy study](doc/pluto-rar-policy-study.md) for its source
semantics, its treatment in the 2008 Pluto papers, and checked no-RAR/RAR
comparisons.

The default path does **not** claim support for the full Pluto transformation
space. It includes the checked phase-aligned tiling route, but it does not by
itself cover transformations such as:

- index-set splitting
- transformations whose correctness would require a stronger structural
  validator than the current checked affine+tiling path
- storage-changing transformations such as scalar privatization or array contraction

Four important extensions now sit beside that default path:

- `--iss`
  - switches to the separate theorem-aligned ISS+affine+tiling route
  - this route is proved by `Opt_with_iss_correct`
- `--parallel-current`
  - switches to theorem-aligned explicit-dimension parallel routes
  - these routes are proved in `ParallelPolOptCorrect.v`
- `--parallel`, `--parallel-strict`, `--parallel --multipar`
  - expose Pluto-hinted checked parallel certification / code generation routes
  - dispatch through the unified `Loop -> ParallelLoop` compiler wrapper
- `--intratileopt`
  - selects a post-tiling affine phase on any tiled route
  - validates affine scheduling, tiling, and intra-tile rescheduling separately

## Native Pluto-style filtered mode

For artifact runs that should look like a Pluto invocation, use:

```sh
./polopt --pluto-compat --explain \
  --tile --smartfuse --nointratileopt --noprevector --nounrolljam \
  --rar --nodiamond-tile --noparallel \
  tests/polopt-generated/inputs/matmul.loop
```

`--pluto-compat` is handled by the OCaml `polopt` driver. It accepts Pluto-like
optimizer flags, rejects unsupported flags with a specific reason, and runs the
corresponding checked route. The regression target is:

```sh
make test-pluto-compat-suite
```

## Main example: covariance (`covcol`)

Input `.loop`:

```text
context(M, N);

for j1 in range(1, (M + 1)) {
  for j2 in range(j1, (M + 1)) {
    for i in range(1, (N + 1)) {
      symmat[j1][j2] = (symmat[j1][j2] + (data[i][j1] * data[i][j2]));
    }
    symmat[j2][j1] = symmat[j1][j2];
  }
}
```

Current optimized output:

```text
context(M, N);

if ((1 <= N && 1 <= M)) {
  for i0 in range(1, (N + 1)) {
    for i1 in range(1, (M + 1)) {
      for i2 in range(i1, (M + 1)) {
        symmat[i1][i2] = (symmat[i1][i2] + (data[i0][i1] * data[i0][i2]));
      }
    }
  }
}
if (1 <= M) {
  for i0 in range(1, (M + 1)) {
    for i1 in range(i0, (M + 1)) {
      symmat[i1][i0] = symmat[i0][i1];
    }
  }
}
```

What changed:

- the accumulation statement and the symmetry-copy statement are split into separate phases
- the accumulation is reordered to run with `i` outermost
- this improves temporal locality for the accumulation phase and matches the Pluto-style optimization family for this kernel

In the previous evaluation for this kernel, with `M = N = 1500`, this transformation achieved about **4x speed-up** on our machine.

## Main tiling example: matrix multiply initialization (`matmul-init`)

Input `.loop`:

```text
context(N);

for i0 in range(0, N) {
  for i1 in range(0, N) {
    C[i0][i1] = 0;
    for i2 in range(0, N) {
      C[i0][i1] = (C[i0][i1] + (A[i0][i2] * B[i2][i1]));
    }
  }
}
```

Current optimized output:

```text
context(N);

if (1 <= N) {
  for i0 in range(0, ((N + 31) / 32)) {
    for i1 in range(0, ((N + 31) / 32)) {
      for i2 in range(max((32 * i0), 0), min(((32 * i0) + 32), N)) {
        for i3 in range(max((32 * i1), 0), min(((32 * i1) + 32), N)) {
          C[i2][i3] = 0;
        }
      }
    }
  }
}
if (1 <= N) {
  for i0 in range(0, ((N + 31) / 32)) {
    for i1 in range(0, ((N + 31) / 32)) {
      for i2 in range(0, ((N + 31) / 32)) {
        for i3 in range(max(0, (32 * i0)), min(N, ((32 * i0) + 32))) {
          for i4 in range(max(0, (32 * i1)), min(N, ((32 * i1) + 32))) {
            for i5 in range(max(0, (32 * i2)), min(N, ((32 * i2) + 32))) {
              C[i3][i4] = (C[i3][i4] + (A[i3][i5] * B[i5][i4]));
            }
          }
        }
      }
    }
  }
}
```

What changed:

- the output now contains explicit tile loops with tile size `32`
- the point-within-tile loops use `max/min` strip-mined bounds
- the initialization and accumulation phases are both tiled, not just rescheduled
- this is the visible shape that the strict suite now classifies as a detected tiled output

## Second-level tiling example: matrix multiply initialization (`matmul-init --second-level-tile`)

Input `.loop`:

```text
context(N);

for i in range(0, N) {
  for j in range(0, N) {
    C[i][j] = 0;
    for k in range(0, N) {
      C[i][j] = (C[i][j] + (A[i][k] * B[k][j]));
    }
  }
}
```

Current optimized output with `./polopt --second-level-tile`:

```text
context(N);

if (1 <= N) {
  for i0 in range(0, ((N + 255) / 256)) {
    for i1 in range(0, ((N + 255) / 256)) {
      for i2 in range(max(0, (8 * i0)), min(((N + 31) / 32), ((8 * i0) + 8))) {
        for i3 in range(max(0, (8 * i1)), min(((N + 31) / 32), ((8 * i1) + 8))) {
          for i4 in range(max((32 * i2), 0), min(((32 * i2) + 32), N)) {
            for i5 in range(max((32 * i3), 0), min(((32 * i3) + 32), N)) {
              C[i4][i5] = 0;
            }
          }
        }
      }
    }
  }
}
if (1 <= N) {
  for i0 in range(0, ((N + 255) / 256)) {
    for i1 in range(0, ((N + 255) / 256)) {
      for i2 in range(0, ((N + 255) / 256)) {
        for i3 in range(max((8 * i0), 0), min(((8 * i0) + 8), ((N + 31) / 32))) {
          for i4 in range(max((8 * i1), 0), min(((8 * i1) + 8), ((N + 31) / 32))) {
            for i5 in range(max((8 * i2), 0), min(((8 * i2) + 8), ((N + 31) / 32))) {
              for i6 in range(max((32 * i3), 0), min(((32 * i3) + 32), N)) {
                for i7 in range(max((32 * i4), 0), min(((32 * i4) + 32), N)) {
                  for i8 in range(max(0, (32 * i5)), min(N, ((32 * i5) + 32))) {
                    C[i6][i7] = (C[i6][i7] + (A[i6][i8] * B[i8][i7]));
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
```

What changed:

- the outer tile loops now step in `256`-sized blocks, while the inner tiles remain `32`
- the generated nest is visibly hierarchical instead of single-level strip-mined
- this is the checked second-level tiling route; it is separate from the ordinary tiling example above

## ISS example: reversal split (`--iss`)

Input `.loop`:

```text
for i in range(0, 100) {
  A[i] = (2 * A[(99 - i)]);
}
```

Current optimized output with `./polopt --iss`:

```text
for i0 in range(1, 50) {
  for i1 in range((i0 + -1), i0) {
    A[i1] = (2 * A[(99 - i1)]);
  }
}
for i0 in range(49, 50) {
  A[i0] = (2 * A[(99 - i0)]);
}
A[50] = (2 * A[(99 - 50)]);
for i0 in range(51, 100) {
  A[i0] = (2 * A[(99 - i0)]);
}
```

What changed:

- the original single interval is split around the reversal midpoint
- the body is unchanged; the visible change is iteration-space partitioning
- this is the characteristic shape of the theorem-aligned ISS route before later scheduling/codegen cleanup

## Parallel example: explicit schedule coordinate (`--parallel-current 0`)

Input `.loop`:

```text
for i in range(0, 100) {
  for j in range(0, 4) {
    A[((4 * i) + j)] = ((2 * A[((4 * i) + j)]) + 2);
  }
}
```

Current optimized output with `./polopt --parallel-current 0`:

```text
parallel for i0 in range(0, 4) {
  for i1 in range(max((32 * i0), 0), min(((32 * i0) + 32), 100)) {
    for i2 in range(0, 4) {
      A[((4 * i1) + i2)] = ((2 * A[((4 * i1) + i2)]) + 2);
    }
  }
}
```

What changed:

- the first padded schedule coordinate is certified parallel and emitted as `parallel for`
- this route is theorem-aligned for explicit coordinates: the optimizer theorem is not inferred from Pluto hints
- the `--parallel` / `--parallel-strict` routes use Pluto hints, while `--parallel-current` fixes the schedule coordinate explicitly; the option name is retained for compatibility

## What is proved

The main theorem-facing compiler wrapper is in
[driver/VerifiedParallelCompilerConfig.v](./driver/VerifiedParallelCompilerConfig.v):

- wrapper: `compile : raw_config -> Loop.t -> imp ParallelLoop.t`
- theorem: `compile_correct`
- verified-config theorem: `compile_verified_correct`

Sequential route-local definitions and theorems are in
[driver/PolOpt.v](./driver/PolOpt.v) and
[driver/PolOptCorrect.v](./driver/PolOptCorrect.v):

- default optimizer: `Opt = Opt_prepared`
- default theorem: `Opt_correct`
- optional ISS optimizer: `Opt_with_iss`
- optional ISS theorem: `Opt_with_iss_correct`

The explicit-dimension parallel optimizer definitions and theorems are in
[driver/ParallelPolOpt.v](./driver/ParallelPolOpt.v) and
[driver/ParallelPolOptCorrect.v](./driver/ParallelPolOptCorrect.v):

- full parallel route: `Opt_parallel_current`
- full parallel theorem: `Opt_parallel_current_correct`
- ISS-enabled full parallel route: `Opt_parallel_current_with_iss`
- ISS-enabled full parallel theorem: `Opt_parallel_current_with_iss_correct`
- identity / affine-only variants are also proved:
  - `Opt_parallel_current_identity_correct`
  - `Opt_parallel_current_affine_correct`
  - `Opt_parallel_current_identity_with_iss_correct`
  - `Opt_parallel_current_affine_with_iss_correct`

The proved passes used by `Opt` are:

1. [src/Extractor.v](./src/Extractor.v)
   - `Extractor.extractor`
   - verified `Loop -> PolyLang` extraction
2. [src/StrengthenDomain.v](./src/StrengthenDomain.v)
   - `strengthen_pprog`
   - conservative strengthening of statement domains by implied parameter guards
3. [driver/PolOpt.v](./driver/PolOpt.v)
   - `checked_affine_schedule`
   - `phase_pipeline_opt_prepared_from_poly`
   - the final verified optimizer route, including checked affine scheduling,
     direct-only tiling validation, and conservative recovery after rejection
   - tiling validation uses the complete semantic band checker in
     [src/TilingBandDirectRuntime.v](./src/TilingBandDirectRuntime.v); it does
     not call the legacy, canonical, or general tiling validators
4. [src/PrepareCodegen.v](./src/PrepareCodegen.v)
   - `prepare_codegen`
   - regularizes the validated program into the codegen-ready representation
5. [polygen/CodeGen.v](./polygen/CodeGen.v)
   - verified polyhedral code generation
6. verified post-codegen cleanup passes:
   - [polygen/LoopCleanup.v](./polygen/LoopCleanup.v)
   - [polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v)

At a high level:

- `Opt_correct` states:
  - if the default verified optimizer returns an optimized loop
  - and that optimized loop runs to a final state
  - then the original input loop can also run to an equivalent final state
- `Opt_with_iss_correct` states the analogous result for the ISS-enabled
  theorem-aligned pipeline

The repository also contains verified parallel components:

- [src/ParallelValidator.v](./src/ParallelValidator.v)
- [src/ParallelCodegen.v](./src/ParallelCodegen.v)
- [driver/ParallelPolOpt.v](./driver/ParallelPolOpt.v)
- [driver/ParallelPolOptCorrect.v](./driver/ParallelPolOptCorrect.v)

Interpretation:

- `--parallel-current d` uses the checked explicit schedule-coordinate parallel pipeline
- `--parallel` / `--parallel-strict` use Pluto-hinted checked one-current routes
- `--parallel --multipar` submits every dimension in the finite candidate list
  constructed for that route to checked multi-current configs; no two-element
  truncation remains
- vector routes accept only a certified innermost loop; automatic rejected
  hints retain the verified sequential result, while explicit
  `--vector-current` rejection is a hard failure
- all of these routes are selected by the unified wrapper theorem rather than by
  changing the sequential `Opt_correct` theorem object
- the route-family flag model itself is documented in
  [doc/POLOPT_FLAG_GUIDE.md](./doc/POLOPT_FLAG_GUIDE.md)

## Operational modes

Important user-facing modes are:

```sh
./polopt file.loop
./polopt --iss file.loop
./polopt --iss --identity file.loop
./polopt --notile file.loop
./polopt --identity file.loop
./polopt --parallel file.loop
./polopt --parallel --parallel-strict file.loop
./polopt --parallel-current 0 file.loop
./polopt --parallel --multipar file.loop
./polopt --second-level-tile file.loop
```

Interpretation:

- default: theorem-aligned affine+tiling pipeline
- `--iss`: theorem-aligned ISS+affine+tiling pipeline
- `--iss --identity`: checked ISS-only split path
- `--notile`: affine-only checked path
- `--identity`: no Pluto scheduling phase
- `--parallel-current d`: theorem-aligned explicit schedule-coordinate parallel route
- `--parallel`, `--parallel-strict`, `--parallel --multipar`: Pluto-hinted checked parallel routes
- `--second-level-tile`: checked second-level tiling route for the
  tiled validation path

## What the default theorem does not cover

`Opt_correct` is a route-local sequential theorem. The wrapper theorem
`VerifiedParallelCompilerConfig.compile_correct` is the end-to-end theorem that
packages accepted sequential, ISS, explicit-coordinate parallel, and Pluto-hinted
parallel configs. Neither theorem says anything about:
- textual `.loop` parsing / elaboration
- Pluto itself
- OpenScop textual parsing / printing details
- witness inference from Pluto phase outputs
- the final OCaml pretty-printer

## What is not proved

The following remain engineering layers around the proved core:

- the textual `.loop` parser / elaborator
- OpenScop textual parsing / printing implementation details
- Pluto itself
- witness inference from Pluto phase outputs
- the final OCaml pretty-printer

## What inputs it supports

`polopt` reads the structured `.loop` syntax documented in [syntax/README.md](./syntax/README.md).
The current frontend supports:

- symbolic parameters via `context(...)`
- structured `for` loops with half-open bounds
- `if` guards formed from affine `<=` / `==` tests joined by `&&`
- scalar and array assignments
- arithmetic using `+`, `-`, `*`, `/` in general RHS expressions
- pure calls in RHS expressions
- ternary expressions in RHS expressions
- float literals in RHS expressions

Still intentionally restricted in affine positions (bounds, guards, indexes):

- affine guards currently support only conjunctions of `<=` / `==` tests; `||` and `!` are rejected
- affine bounds / guards / indexes accept only constants, variables, affine sums, and constant-multiplied subexpressions
- division is rejected in affine bounds / guards / indexes
- general calls in affine bounds / guards / indexes
- non-affine ternaries in affine bounds / guards / indexes

## Assumptions and model boundary

The current `polopt` frontend works over the lightweight `SInstr` model rather than full CompCert C semantics.
That means:

- calls are treated as pure computations
- the frontend does not model realistic floating-point precision/rounding effects
- the instantiated instruction model still assumes the non-aliasing / compatibility conditions required by the verified core
- practical C-level issues such as overflow, aliasing, and full floating-point semantics remain separate integration work

So the right reading is:

- the optimizer uses **Pluto's optimization choices** under the relevant flag
  set for the selected mode
- the surrounding extraction / validation / code generation path has a formal correctness argument in the current loop-language model
- users should read current floating-point and overflow behavior under the current simplified model assumptions

## Benchmark behavior

The generated strict regression suite is under [tests/polopt-generated](./tests/polopt-generated).
Current strict proved-path status:

- total inputs: `62`
- succeeded: `62`
- changed: `59`
- unchanged: `3`
- nontrivially changed: `59`
- automatically detected tiled outputs: `46`

These numbers are the current observed snapshot on the manifest-owned corpus.
The default CI gate does not assert those exact counts. It enforces the
thresholds and required representative cases declared in
[tests/polopt-generated/strict_suite_manifest.json](./tests/polopt-generated/strict_suite_manifest.json).

Interpretation:

- scheduling decisions come from Pluto itself
- the strict `polopt` path now succeeds on the full generated benchmark suite
- the stronger `nontrivial_changed` metric ignores only trivial loop-variable
  alpha-renaming and whole-program outer guard wrappers
- the `detected_tiled` metric is intentionally narrower than `changed`; it
  only counts outputs with explicit strip-mined tile structure
- across the suite, the resulting loop transformations follow the same optimization families as the corresponding C-path Pluto runs under the exact flag set shown above
- in that sense, `polopt` currently covers the checked affine route and the
  checked phase-aligned tiling route under the supported Pluto setup, with
  verified extraction / validation / code generation around them
- this should still not be read as support for the full Pluto transformation
  space: the checked state-preserving wrapper covers the supported schedule,
  tiling, ISS, and annotation routes, while storage-changing transformations
  remain outside the current `State.eq` theorem family

One practical exception is performance on `advect3d`:

- it succeeds semantically
- but `CodeGen.codegen` is still noticeably slower than Pluto on that case
- the slowdown is in code generation, not in parsing, Pluto, or validation

Current status after the singleton-piece fast-path repair:

- identity route: about `5.4s -> 1.2s`
- affine-only route: about `40s -> 22.9s`

So the first codegen repair is already proved and integrated, but `advect3d`
remains a real compile-time stress case rather than a solved problem.

## How to run

Build with the standard sequence from [README.md](./README.md), then run:

```sh
./polopt file.loop
```

Useful modes:

```sh
./polopt --extract-only file.loop
./polopt --debug-scheduler file.loop
./polopt --profile-stages file.loop
./polopt --iss file.loop
./polopt --parallel file.loop
./polopt --parallel-current 0 file.loop
./polopt --iss --parallel-current 0 file.loop
./polopt --second-level-tile file.loop
./polopt --diamond-tile file.loop
./polopt --full-diamond-tile file.loop
```

## How to write your own example

Start from a small structured loop fragment, for example:

```text
context(N, M);
for i in range(0, N) {
  for j in range(0, M) {
    C[i][j] = A[i][j] + B[i][j];
  }
}
```

Guidelines:

- use `context(...)` for symbolic parameters
- use half-open loop bounds `range(lb, ub)`
- keep bounds, guards, and indexes affine
- use calls/ternaries only in RHS expressions, not in affine control/index positions

## How to test

The remote regression gate builds once with
[tools/ci/run_ci_build.sh](./tools/ci/run_ci_build.sh) and runs isolated shards
through [tools/ci/run_ci_shards.sh](./tools/ci/run_ci_shards.sh).
[tools/ci/run_ci.sh](./tools/ci/run_ci.sh) remains the sequential in-container
entry point.
Locally, the main commands are:

```sh
bash tools/ci/check_pluto_baseline.sh
make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
make test
opam exec -- make test-iss-pluto-suite
opam exec -- make test-iss-pluto-live-suite
opam exec -- make test-parallel-current-suite
opam exec -- make test-second-level-tile-suite
opam exec -- make test-polopt-loop-suite
opam exec -- make test-diamond-tiling-suite
opam exec -- make test-end-to-end-c-correctness
opam exec -- make test-extracted-zero-fallback
```

If you only want to refresh the generated strict-suite corpus for downstream
whole-C harnesses, without running the strict checker gate, use:

```sh
opam exec -- make materialize-polopt-loop-suite
```

Heavier end-to-end performance checks are intentionally **not** part of default
CI. The default gate includes the diamond suite, per-case strict-loop effect
contracts, handwritten executable correctness checks, and executable checks for
all 62 generated cases; it does not assert the exact current `59` / `46`
snapshot shown above. The current non-default performance workflows are:

- repeated handwritten cases in [tests/end-to-end-c](./tests/end-to-end-c)
- generated whole-C performance campaigns in
  [tests/end-to-end-generated](./tests/end-to-end-generated)

The one-command local perf refresh is:

```sh
opam exec -- make test-end-to-end-generated-perf-refresh
```

That command refreshes:

- the per-case best-pipeline search
- the fixed Markdown report under
  [tests/end-to-end-generated/BEST_PIPELINES.md](./tests/end-to-end-generated/BEST_PIPELINES.md)
- the generated `perf` suite run that uses the chosen best pipeline for each
  case

Current generated `perf` snapshot:

- cases: `62`
- selected-best results with `exact_match=true`: `62 / 62`
- the concrete current distribution is reported in:
  - [tests/end-to-end-generated/BEST_PIPELINES.md](./tests/end-to-end-generated/BEST_PIPELINES.md)
  - `tests/end-to-end-generated/best_pipeline_report.json`

Interpretation:

- `parallelized_loop=true` in the report means the chosen route emitted a real
  verified `parallel for`
- `parallel_4` / `iss_parallel_4` are only eligible best-pipeline candidates
  when they emit a real `parallel for`; purely sequential fallbacks are not
  allowed to win the "parallel" slots anymore
- `iss` / `iss_parallel_4` means the `--iss` route measured best; it does
  **not** by itself prove that Pluto actually performed ISS statement splitting
  on that generated case

The generated per-case results live under:

- [tests/polopt-generated/cases](./tests/polopt-generated/cases)

The strict suite now reports progress case by case and uses a `300s` per-case
timeout instead of a suite-wide timeout, so slow kernels such as `advect3d` are
visible during the run instead of appearing to hang silently.

## Key source files

Compiler / CLI entry:
- [syntax/SLoopMain.ml](./syntax/SLoopMain.ml)
- [syntax/SLoopCli.ml](./syntax/SLoopCli.ml)
- [syntax/SLoopRoute.ml](./syntax/SLoopRoute.ml)
- [syntax/SLoopDispatch.ml](./syntax/SLoopDispatch.ml)
- [syntax/SLoopProfile.ml](./syntax/SLoopProfile.ml)

Frontend bridge to the verified optimizer:
- [syntax/SPolOpt.v](./syntax/SPolOpt.v)

Final optimizer definition and theorem:
- [driver/PolOpt.v](./driver/PolOpt.v)

Key passes:
- [src/Extractor.v](./src/Extractor.v)
- [src/StrengthenDomain.v](./src/StrengthenDomain.v)
- [src/ISSValidator.v](./src/ISSValidator.v)
- [src/ISSValidatorCorrect.v](./src/ISSValidatorCorrect.v)
- [src/PrepareCodegen.v](./src/PrepareCodegen.v)
- [src/ParallelValidator.v](./src/ParallelValidator.v)
- [src/ParallelCodegen.v](./src/ParallelCodegen.v)
- [polygen/CodeGen.v](./polygen/CodeGen.v)
- [polygen/LoopCleanup.v](./polygen/LoopCleanup.v)
- [polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v)
