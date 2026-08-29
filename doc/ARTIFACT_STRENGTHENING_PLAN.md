# Artifact Strengthening Plan

Date: 2026-03-19

This note is not a paper-outline note. It is the engineering/research TODO for
turning the current PolCert/PolOpt artifact into a stronger, more
full-fledged verified polyhedral-compilation artifact.

Current baseline:

- theorem-aligned affine+tiling optimizer route
- theorem-aligned optional ISS route
- theorem-aligned explicit-dimension parallel route
- strict generated-loop suite passes (`62 / 62`)
- ISS fixed-fixture and live Pluto suites pass in CI
- Pluto bug reproducer target exists for the `matmul --parallel` hint case
- source-model fidelity is already structurally aligned on the current suite
- handwritten whole-C harness exists under `tests/end-to-end-c`
- generated whole-C harness exists under `tests/end-to-end-generated`
- generated perf search now records a 62-case best-pipeline table
  (`BEST_PIPELINES.md`)

The next step is therefore not "add one more theorem in isolation". It is to
strengthen the artifact along the same dimensions a real polyhedral compiler is
judged on:

1. whole-C end-to-end usability
2. code-generation scalability
3. bug-finding value against Pluto itself
4. broader transformation-family coverage, especially diamond tiling

## 1. Whole-C End-to-End Wrapper And Performance Harness

### Goal

Move beyond `.loop -> optimized .loop` testing and add an end-to-end harness
that behaves more like Pluto's `polycc` workflow on C code with a marked
polyhedral region.

The desired story is:

```text
original C with a target scop
-> extract / or load the corresponding loop fragment
-> run theorem-aligned polopt pipeline
-> splice optimized loop back into the C wrapper
-> compile and run correctness + performance checks
```

This does not replace the current loop-language suite. It complements it.

### Why this matters

- It provides a stronger artifact claim than "verified loop fragment optimizer".
- It lets us measure optimization benefit, not only validation success.
- It matches how Pluto is actually consumed in practice: as a source-to-source
  optimizer embedded in a larger C benchmark or kernel harness.

### Existing starting points

- `tools/generate_pluto_loops.py`
- `tests/polopt-generated/`
- current `polopt` examples and strict loop suite
- Pluto's own `polycc` whole-C code-generation flow

### Concrete tasks

1. Add a new whole-C benchmark directory, for example:
   - `tests/end-to-end-c/`
2. For each selected benchmark:
   - keep the original C wrapper/harness
   - keep a canonical extracted `.loop`
   - keep a splice template showing where the optimized loop should go back
3. Add a small driver script, for example:
   - `tools/end_to_end_c/run_case.py`
   - `tools/end_to_end_c/run_suite.py`
4. The driver should support at least:
   - baseline original C
   - Pluto-generated optimized C
   - `polopt`-optimized-and-spliced C
5. Add correctness checks:
   - compare outputs against the original executable
   - compare PolOpt-spliced executable against Pluto-spliced executable when
     applicable
6. Add performance checks:
   - compile-time timing
   - runtime timing
   - separate reporting for optimization overhead vs kernel speedup

### Initial benchmark targets

Use kernels that already expose clear visible optimization families in the
current artifact:

- `covcol`
- `matmul`
- `matmul-init`
- `wavefront`
- one ISS-positive periodic/reversal kernel
- one explicit parallel kernel

### Acceptance target

This workstream is successful once the artifact can report, for a small but
real benchmark subset:

- compile success
- output agreement
- optimization family preserved
- runtime speedup of optimized code over baseline original code

### Current status

This workstream is now partially complete:

- handwritten whole-C harness:
  - `matmul`, `reverse_iss`, plus perf-sized variants
- generated whole-C harness:
  - covers the 62 generated regression cases
  - exposes a per-case best-pipeline search across:
    - default no-ISS affine+tiling
    - affine-only
    - ISS
    - parallel (`4` threads)
    - ISS+parallel (`4` threads)
    - identity fallback
  - emits:
    - `best_pipelines.json`
    - `best_pipeline_report.json`
    - `BEST_PIPELINES.md`
- the one-command local refresh is:
  - `opam exec -- make test-end-to-end-generated-perf-refresh`

The one-repeat correctness tier is now part of default CI. Repeated timing,
pipeline search, and tuning remain outside the default gate.

### Closed review follow-ups (2026-07-19)

The April harness gaps are now implemented: strict generated-corpus invariants
are CI gates, subprocess timeouts cover compiled benchmarks, numeric summaries
use documented tolerances, and the isolated CI shards cover one-level route
discipline, Pluto compatibility,
parallel-current, vector-current, second-level tiling, and the Pluto-backed
diamond matrix.

The one-level matrix is a route-discipline gate: it excludes fallback and
checks exact route/alarm reporting across the CLI combinations. It does not
assert a distinct optimization effect for every flag in every combination.
The compatibility, parallel-current, vector-current, and diamond suites carry
the representative effect checks.

## 2. Codegen Performance: `advect3d`

### Goal

Turn `advect3d` from "semantic success but slow code generation" into a normal
artifact case.

Current understanding from existing notes:

- Pluto itself is not the bottleneck
- validation is not the bottleneck
- the remaining cost is in `CodeGen.codegen`

### Why this matters

- It is currently the clearest counterexample to "the verified path is a
  practical compiler pass".
- Fixing it improves both the artifact and the paper story.
- It gives us a concrete systems result, not only another proof result.

### Concrete tasks

1. Add stage timing for the `polopt` path:
   - extraction
   - strengthening
   - affine/tiling/ISS validation
   - `prepare_codegen`
   - `CodeGen.codegen`
   - cleanup / pretty printing
2. Add a reproducible timing target for `advect3d`.
3. Profile `CodeGen.codegen` specifically on the generated polyhedral program.
4. Audit common sources of blowup:
   - repeated recursive expression rebuilding
   - repeated traversal/normalization of the same schedule or access data
   - quadratic list concatenation / nested loop-body assembly
   - avoidable recomputation across statements
   - cleanup passes re-walking already-normalized subtrees
5. Introduce a regression check:
   - `advect3d` compile time should stay below a documented bound on the
     reference machine/container

### Current profiling finding

Current `advect3d` profiling shows that the dominant cost is not validation
or Pluto itself. It is code generation, specifically:

- `codegen_ast_generate`
- then `codegen_polyloop_simpl`

On the affine-only checked route, the prepared codegen input still has only
`4` source `PolyInstr`s, but `ASTGen.generate_loop_many` expands them into
`33` instruction leaves and `1276` polyloop nodes. This means the current
problem is driven by internal codegen cell decomposition rather than by
pre-codegen statement explosion in the verified pipeline.

### Clean-build reproduction baseline

On 2026-07-18, the current Docker workspace was rebuilt from `make clean` with:

```sh
make clean
make depend
opam exec --switch=polcert -- make -j8 polopt polcert
```

The measured build used `15:36.07` wall time, `2262.00s` user CPU,
`685.87s` system CPU, and `11,768,328 KiB` peak resident memory. This is a
clean Coq extraction plus OCaml link measurement inside the existing artifact
container, not a Docker image build. This single `-j8` observation reached
about 11.2 GiB peak RSS; it is not yet a machine-independent memory requirement.
Artifact instructions should budget about 20 minutes on a comparable machine.
Dynamic suite times must be recorded separately because they also depend on
Pluto and solver runs.

Final-gate measurements used two containers. The long-lived `gifted_curie`
container measured:

- Pluto compatibility matrix: `132 / 132` in `325.64s`;
- full 69-fixture identity-composition exploration: `332.39s`.

The strict loop corpus exposed one additional slow case. A focused `tce` run
completed the optimizer invocation in `324.91s` (`5:14.59` for the materializer
process, `38,572 KiB` peak RSS). The manifest therefore keeps the `300s`
default but assigns `tce` a `600s` case budget. This is an observed runtime and
timeout allowance, not a performance claim.

A disposable container with `/tmp/polcert-final-gate-build` mounted at `/work`
measured the full second-level tiling suite at `954.751s`. The hardened 90-case
one-level route gate passed against the clean binary in `gifted_curie` in
`184.21s`.

These measurements motivated outer timeouts of `900s` for identity-composition
exploration and `1800s` for the second-level suite. They are timeout budgets,
not expected runtimes.

On 2026-07-19, `artifact-check-full` completed against the prepared clean
binary. The outer `/usr/bin/time` process reported `44:02.91` wall time
(`2618.67s` user CPU, `20.78s` system CPU, and `204,020 KiB` peak RSS), while
the artifact runner's monotonic per-stage measurements sum to `45:33.9`.
Because the two clocks disagreed by about 91 seconds, the larger monotonic sum
is the conservative reproduction time. Major stage times were:

- identity-composition exploration: `341.4s`;
- one-level route discipline: `183.6s`;
- Pluto compatibility: `334.9s`;
- second-level tiling: `997.7s`;
- diamond tiling: `152.2s`;
- strict 62-case loop corpus: `614.8s`;
- parallel-current: `49.1s`;
- vector-current: `29.5s`.

This full-check time excludes the clean proof/extraction build. Running the
measured clean build and full check serially requires about one hour on the
measured container; artifact instructions should budget roughly 65 minutes,
excluding the Docker image build itself.

After the identity-like second-level direct route was added, two serial
core-change rebuilds from `src/TilingBandScheduleValidator.v` through extracted
`polopt` took `2020s` (`33:40`) and `1707s` (`28:27`) in the long-lived
`gifted_curie` container. The final focused gates measured `1040s` (`17:20`)
for the second-level suite, `332s` (`5:32`) for all 133 Pluto-compatibility
checks, and `209s` (`3:29`) for the 90-case one-level route matrix. These are
observed serial runtimes on a prepared container, not universal performance
claims; a clean artifact run still needs the larger budget above.

On 2026-07-23, an isolated pre-final snapshot containing the mixed
second-level direct checker completed `make -j8 extraction/STAMP` in
`36:11` wall time.  The parallel portion had drained before the last large
proof and extraction steps: `driver/ExtractedPipelineCorrect.v` ran alone for
more than eight minutes, and the final `extraction/extraction.v` pass also ran
single-threaded.  `make -f Makefile.extr depend` then completed in `1.43s`.
This is a proof/extraction measurement in an already prepared container, not a
Docker image build or a final artifact runtime.  The final zero-fallback
snapshot must be measured again after its two-state dispatcher is extracted.

The prepared `polcert-zero-fallback-final` container then checked the final
source-like second-level zero-row normalization through the complete extracted
pipeline.  The full second-level suite completed in about `16:50`, including
53 manifest acceptances, 5 negative cases, 16 diamond consumer acceptances,
4 explicit vector rejections, and the standalone source-like OpenScop pair.
The independent one-level matrix completed in `198.11s`, with 84 direct
acceptances, 0 tiling-validation fallbacks, and 6 explicit vector rejections.
These are warm-container regression times; the final clean build and artifact
run remain the publication-facing reproduction measurements.

On 2026-07-24, profiling identified module-interface expansion, rather than a
slow proof tactic, as the dominant cost of rebuilding the zero-fallback
snapshot.  In particular, profiling
`driver/SParallelPolOptBridge.v` before narrowing the runtime interface took
`6:04.81` wall time and `13,942,976 KiB` peak RSS, while all Ltac execution in
that file totaled only `0.384s`.  Profiling
`src/TilingBandScheduleValidator.v` reported `23.37s` wall time,
`1,540 MiB` peak RSS, and `7.171s` total Ltac time; no individual tactic took
more than about `0.3s`.

The repair seals the tiling runtime behind the four fields used by the
drivers--the route type, its Boolean observation, the runtime validator, and
its correctness theorem--and removes an unused correctness-functor instance
from `SParallelPolOptBridge`.  This reduced:

- `ParallelPolOptCorrect.vo` from about `501 MiB` to about `157 MiB`;
- `SParallelPolOptBridge.vo` from about `159 MiB` to about `29 MiB`;
- `VerifiedParallelCompilerConfig.vo` from about `274 MiB` to about `142 MiB`;
- `ExtractedPipelineCorrect.vo` from about `183 MiB` to about `97 MiB`.

After the change, the same bridge profile completed in `1:00.75` with about
`3.77 GiB` peak RSS.  A serial rebuild of the affected proof chain through
`ExtractedPipelineCorrect.vo` took `6:04.44` and peaked at about `9.60 GiB`.
Fresh extraction then took `1:37.23` and `7,338,560 KiB` peak RSS; rebuilding
and linking both `polopt` and `polcert` took `2:09.32` and `877,776 KiB` peak
RSS.  These three measurements describe a prepared-container core-change
rebuild, not a clean repository or Docker-image build.  Before the interface
repair, the corresponding serial extraction-plus-`polopt` rebuild took
`1:02:00` and peaked at `21,646,436 KiB`.

The final warm-container `artifact-check-full` run completed successfully on
the same date.  The outer timer reported `34:08.70` wall time, `2022.61s` user
CPU, `21.02s` system CPU, and `126,488 KiB` peak RSS.  Per-stage monotonic
measurements totaled `35:04.95`; the latter is the conservative dynamic-suite
estimate.  Major stages were:

- identity-composition exploration: `140.0s`;
- one-level route discipline: `163.8s`;
- Pluto compatibility: `269.2s`;
- second-level tiling: `1110.0s`;
- diamond tiling: `106.0s`;
- strict 62-case loop corpus: `247.4s`;
- parallel-current: `31.7s`;
- vector-current: `10.6s`.

Its machine-readable route summary reports 20 direct-route cases with zero
fallbacks, 84 accepted one-level compositions with zero fallbacks and 6
explicit vector rejections, 53 accepted and 5 rejected second-level manifest
cases, and 61 strict-corpus permutable-band routes plus one no-loop case.  The
final release budget must still use a clean image build followed by this
dynamic suite; the measurements above establish the prepared-container
baseline only.

A subsequent no-bind-mount release-candidate build started from `make clean`
inside the pinned Docker environment.  The conservative command explicitly
built `extraction/STAMP` before requesting both binaries; because the build
graph revisited part of the proof and extraction chain, it took `47:31.99`
wall time and `9,598,656 KiB` peak RSS.  The release Docker target now requests
`polopt`, `polcert.ini`, and `polcert` in one `make -j1` invocation so the
shared proof and extraction prerequisites are built once.

The complete dynamic suite then ran without a source mount against those
fresh binaries.  All 27 checks passed in `34:38.50` wall time with
`864,376 KiB` peak RSS; the sum of per-check monotonic times was `2151.04s`.
The dominant checks were the second-level suite (`1118.1s`), Pluto
compatibility (`270.7s`), the strict loop corpus (`256.9s`), one-level route
coverage (`165.6s`), identity compositions (`140.9s`), and diamond tiling
(`106.8s`).  This run used Pluto commit
`488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02`.

Additional tactic profiles rule out a hidden slow tactic in the newly added
tiling proof modules:

- `TilingBandScheduleValidator.v`: `22.21s` wall, `6.349s` total Ltac, and
  `0.265s` maximum for one tactic call;
- `TilingBandMixedSecondValidator.v`: `9.26s` wall, `0.939s` total Ltac, and
  `0.027s` maximum;
- `TilingBandPhaseScalarValidator.v`: `15.12s` wall, `0.220s` total Ltac, and
  `0.015s` maximum;
- `TilingBandDirectRuntime.v`: `31.51s` wall, `0.083s` total Ltac, and
  `0.009s` maximum.

The remaining compile cost is therefore dominated by kernel checking and
module/functor elaboration, not proof-search tactics.  A rebuild of the default
multi-stage Docker `development` target also passed; the first build after
pinning the base-image digest took `5:57.59`.  The dedicated `artifact` target
additionally compiles the binaries in-image and requires an exact source
commit, release tag, source-archive hash, and observed image digest before its
claim suite will run.

The pre-fast-path comparison against the identity route was:

- identity route:
  - `4` instruction leaves
  - `229` polyloop nodes
  - about `5.7s` total
- affine-only route:
  - `33` instruction leaves
  - `1276` polyloop nodes
  - about `39s` total

So the next repair target should be treated as:

- reducing schedule-induced polyhedral fragmentation before or during
  `ASTGen.generate_loop_many`

rather than treating `CodeGen` as uniformly slow on the unscheduled source
program.

Current code-level candidate for the next iteration:

- add a specialized fast-path for single-statement pieces inside
  `generate_loop_many`

That should be treated as a separate proof/benchmark task. It is a plausible
way to avoid paying the full split-and-sort recursion cost once a fragmented
schedule has already isolated a piece down to one statement, but it should not
be merged until it is both proved and measured.

### Current status after the first fast-path repair

That fast-path has now been implemented and measured. Current numbers on the
container baseline are:

- identity route:
  - before: about `5.4s`, `229` raw polyloop nodes, `1536` constraints
  - after: about `1.16s`, `85` raw polyloop nodes, `184` constraints
- affine-only route:
  - before: about `40s`, `1276` raw polyloop nodes, `9352` constraints
  - after: about `22.4s`, `634` raw polyloop nodes, `2722` constraints

So the first repair already cuts the dominant `advect3d` codegen hotspot
substantially. The remaining work is no longer "make it stop exploding
catastrophically", but "continue reducing schedule-induced fragmentation on
harder affine outputs".

### Pluto comparison and current conclusion

It is important not to explain the remaining gap away as "verification is
expensive". On the same `advect3d` benchmark, Pluto's own non-tiled codegen is
still much faster:

- Pluto `--pet --notile --noparallel --nounrolljam --nointratileopt --nodiamond-tile`
  finishes in about `0.47s`
- the current verified affine-only route is still about `21-22s`

So the remaining gap is not an unavoidable proof tax. It reflects a real
algorithmic difference in the current code-generation strategy.

The main structural difference is:

- Pluto emits a global CLooG input from statement domains and scattering
  functions, then lets CLooG generate a unified CLAST.
- the verified path recursively builds a piecewise `PolyLoop` tree via
  `ASTGen.generate_loop_many`, then simplifies it, then lowers it.

This matters because the current verified simplifier only performs
context-sensitive polyhedral simplification. It does **not** perform strong
cross-piece region merging. In particular, after the first fast-path repair:

- `codegen_ast_generate` still dominates (`~17.4s`)
- `polyloop_raw.nodes` is still `634`
- `polyloop_simpl.nodes` is also `634`

So the remaining slowdown is best understood as:

- schedule-induced region fragmentation
- combined with a codegen path that is still mostly recursive/piecewise rather
  than globally merged

This also means the next candidate repair should not be chosen casually. A
"simple cleanup" inside `LoopCleanup` or `LoopSingletonCleanup` is unlikely to
help much, because those passes happen after the main explosion and the hotspot
remains `codegen_ast_generate`, not final cleanup.

Current engineering conclusion:

- the singleton-piece fast-path was a justified simple repair and should stay
- there is no equally obvious second small fix with the same expected payoff
- further large improvements will likely require a more structural change:
  - earlier merging of equivalent regions
  - a less fragmenting intermediate representation
  - or a more CLooG-like global codegen strategy

### Deliverables

- a timing note or CSV in `doc/`
- a dedicated `advect3d` compile-time target
- the codegen repair itself

Current concrete artifact hooks:

- `make profile-advect3d-codegen`
- `make profile-advect3d-codegen-identity`
- `tools/perf/run_stage_profile.py`

These make the current hotspot reproducible without having to reconstruct the
exact `polopt --profile-stages` invocation by hand.

## 3. Pluto Bug Work

### Goal

Make the artifact explicitly useful as a checker for external optimizer bugs or
unsafe heuristics in Pluto.

The initial parallel-hint candidate has now been superseded by two minimized,
executable silent-miscompilation witnesses. See
`doc/pluto-whitebox-correctness-audit.md`.

### Concrete tasks

1. Introduce a bug-case taxonomy:
   - suspected
   - reproduced
   - validator-catches
   - minimized
   - upstreamed
2. Add a dedicated reproducibility directory, for example:
   - `tests/pluto-bugs/`
3. For each bug candidate, keep:
   - source input
   - exact Pluto invocation
   - expected bad Pluto artifact or behavior
   - expected PolCert behavior
4. Keep searching beyond the current parallel and unroll-jam cases in:
   - ISS outputs
   - `--readscop` paths
   - second-level / diamond / parallel interactions
5. Prefer small minimized reproducers over broad anecdotal discussion.

### Acceptance target

At least one case should become a complete artifact-grade case study:

- reproducible in CI or a dedicated script
- explained locally in the repo
- suitable for upstream reporting to Pluto

### Current status

The artifact now contains seven cases under `tests/pluto-bugs/`: the original
unsafe matmul hint and six confirmed silent miscompilations, one of which is
fixed in the current Pluto baseline. The automatic GLPK LP scheduler case
produces incompatible component scales and changes
`802469374803681347` to `11412027514774867379` without a supplied schedule or
control file. In addition, the vanished-loop parallel case produces `10000`
versus `2499`, no-tile unroll-jam produces `15` versus `1`, the optional `.fst`
interface accepts a statement reversal that produces `100` versus `0`, and
`--innerpar` after tiling corrupts a two-dimensional recurrence. The pure
diamond/no-intratile case produced `20` versus `18` because a mandatory
hyperplane restore was incorrectly gated; Pluto commit `56b6669` fixes it.
Checked PolCert boundaries reject the automatic and supplied illegal affine
schedules, parallel overlay, and mixed-scalar diamond candidate while retaining
valid tiling and safe local unrolling. The typed `diamond-stencil` positive case
separately exercises proved code generation for supported pure diamond tiling.
`make test-pluto-bugs` executes the adversarial boundaries in CI. The
separate ISS suite accepts a complete two-cut partition while rejecting both a
three-cut/four-piece metadata mismatch and a missing sign region.

## 4. Diamond Tiling Track

### Goal

Keep the checked diamond tiling path artifact-grade as its surrounding Pluto
flag surface grows.

This is no longer a design-only workstream. The current implementation has a
checked phase-aligned diamond route and native Pluto-compatible tests for the
main route combinations. The remaining work is fixture breadth and output
polish, not route closure.

### Current status

The implemented route follows the architecture from the design notes:

- import and validate the diamond-aware affine midpoint
- validate the `mid_diamond -> posttile` boundary with the direct-only
  dispatcher: ordinary/common bands, program-wide semantic bands,
  uniform grouped/interleaved second-level bands, and the phase-aware mixed
  second-level bridge
- validate the final post-tile affine cleanup boundary
- regenerate code through the PolOpt code generator

The executable coverage now includes:

- sequential `--diamond-tile`
- `--full-diamond-tile`
- ISS plus diamond
- second-level diamond
- Pluto-hinted parallel diamond
- Pluto-hinted multipar diamond
- native explicit-current diamond parallelization

The artifact hook is:

```bash
opam exec -- make test-diamond-tiling-suite
```

The default `artifact-check` also runs the diamond suite.

### Remaining tasks

1. Broaden effect fixtures for:
   - `--full-diamond-tile`
   - `--diamond-tile --iss`
   - `--diamond-tile --second-level-tile`
   - `--diamond-tile --parallel --multipar`
2. Polish the checked raw-codegen output for singleton-loop cleanup cases where
   the checked raw route is correct but less readable.
3. Keep identity-diamond rejected unless a distinct Pluto output effect is
   found. The current bounded search over the regression corpus found
   `--identity --tile --diamond-tile` identical to ordinary identity tiling.

### Non-goals

- Do not claim identity-diamond support without a route-specific output effect.
- Do not turn diamond tests into performance claims.
- Do not turn the checked multi-current route into a performance or OpenMP
  scheduling claim. It may annotate every certified candidate dimension, but
  the artifact claim remains semantic preservation plus observed optimization
  effects in the regression suite.

Any stronger scheduling, load-balance, or performance claim belongs to a later
paper story, not to this artifact-coverage track.

## 5. Priority Order

Recommended implementation order:

1. whole-C end-to-end wrapper/harness
2. `advect3d` codegen performance repair
3. Pluto bug reproducibility track
4. diamond-tiling fixture broadening
5. factor-based variable-bound unroll-jam post pass
6. checked scalar-private storage rewrite

Rationale:

- The first four strengthen the artifact story without changing the core
  semantic model.
- The checked constant-bound unroll post pass is now present, including
  `--ufactor` acceptance on that subset and a whole-C compile/run smoke case.
  General variable-bound unroll-jam and full scalar privatization remain real
  semantic/codegen extensions. They should be implemented only as
  theorem-facing PolOpt transformations, not as Pluto pass-through.

## 6. Definition Of Success For The Next Iteration

The artifact should be considered meaningfully stronger once it can do all of
the following:

- run a small whole-C benchmark subset end to end
- show real runtime speedups of optimized code
- no longer treat `advect3d` as an outlier compile-time case
- contain at least one strong Pluto-bug case study
- keep diamond, second-level, vector, parallel, and multipar compatibility
  routes under executable artifact checks
- accept the checked constant-bound `--unrolljam` subset, including
  `--ufactor` as a compatibility flag on that subset, compile/run its generated
  C in artifact-check, and explicitly reject the remaining semantic gaps
  (general variable-bound unroll-jam and full scalar privatization) until their
  checked transformations exist

At that point, the artifact is no longer only "proved and correct on loop
fragments". It starts to look like a genuinely usable verified polyhedral
compiler artifact.

## 7. Release Artifact TODO

After the proof-cleanup pass and paper claims are frozen:

1. create a release tag for the exact reviewed commit;
2. build a fresh Docker image from that tag without a source bind mount;
3. record the image digest, Git revision, Pluto baseline, Coq/OCaml versions,
   build command, and host resource limits;
4. run `artifact-check-full` inside the image and retain its JSON summary;
5. publish the measured clean-build and dynamic-suite times, including the
   `tce` slow-case allowance and the roughly 65-minute sequential budget
   observed on the current container.

The release image is not complete until the digest and the passing
`artifact-results.json` refer to the same tagged source snapshot.
