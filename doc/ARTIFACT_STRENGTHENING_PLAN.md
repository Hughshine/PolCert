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

This harness is intentionally not part of default CI.

### Immediate review follow-ups (2026-04-10)

Recent review passes identified several harness / coverage gaps that should be
tracked as explicit artifact-TODO items until they are re-verified and closed:

1. CI currently materializes the generated `polopt` regression corpus, but does
   not yet assert the strict checker invariants (`--expect-total`,
   `--min-changed`, `--require-tiled`). The CI path needs to run the checker
   stage as a real gate, not only refresh the materialized outputs.
2. `--timeout-seconds` needs to cover not only `polopt` itself but also the
   compiled benchmark executables in both handwritten and generated end-to-end
   harnesses. A hung baseline or optimized binary should fail the case rather
   than stall the suite.
3. The generated whole-C harness should compare numeric summaries with a small
   documented tolerance for floating-point drift, especially on `--parallel` /
   OpenMP paths, instead of requiring exact zero drift everywhere.
4. Public user modes need direct automated regression coverage:
   - theorem-aligned `--parallel-current`
   - `--second-level-tile`
   The current CI surface is still too indirect to guarantee that those routes
   have not silently regressed.

These remain TODO items until the fixes are landed and then re-checked in the
real container / CI path.

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

The current comparison against the identity route is also important:

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

Current best candidate already in-repo:

- `doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md`

That case already has the right shape:

- Pluto proposes a parallel dimension
- the PolCert checked route rejects it or prefers a safer dimension
- this demonstrates practical value beyond theorem self-containment

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
4. Start with the current parallel-hint case, then search for more in:
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

The first artifact-grade bug reproducer now exists as:

- `tools/pluto_bugs/run_matmul_parallel_hint.py`
- `make test-pluto-bug-matmul-parallel-hint`

This case reproduces the current behavior where:

- Pluto hints current dimension `0` for `matmul`
- PolCert's checked parallel validator rejects that hinted dimension
- the non-strict frontend falls back to certified current dimension `1`
- the strict frontend keeps the optimized loop sequential

That is enough to keep the bug track inside the artifact itself rather than as
just a prose note.

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
- validate the `mid_diamond -> posttile` tiling boundary with the existing
  tiling relation
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

Relevant existing notes:

- `doc/pluto-comprehensive/second-level-and-diamond-design.md`
- `doc/pluto-comprehensive/polopt-second-level-diamond-support.md`
- `doc/pluto-comprehensive/tiling-validation-design.md`
- `doc/DIAMOND_TILING_IMPLEMENTATION_TODO.md`

### Remaining tasks

1. Broaden effect fixtures for:
   - `--full-diamond-tile`
   - `--diamond-tile --iss`
   - `--diamond-tile --second-level-tile`
   - `--diamond-tile --parallel --multipar`
2. Add strict-mode checks for Pluto-hinted diamond parallel routes, so the
   suite distinguishes "hint accepted" from "checked fallback".
3. Polish raw-codegen fallback output for singleton-loop cleanup cases where
   the checked raw route is correct but less readable.
4. Keep identity-diamond rejected unless a distinct Pluto output effect is
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
