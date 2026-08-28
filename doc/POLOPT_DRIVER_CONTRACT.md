# PolOpt Driver Contract

Status: design target for the artifact-facing driver. This document separates
the intended interface from the current v10 implementation. A feature is not
part of the final contract until the acceptance tests in this document pass.

## 1. Product Boundary

`polopt` is the verified optimizer driver. It accepts the optimizer-facing
options used by Pluto, asks Pluto to produce transformation candidates, checks
each semantic transformation, and emits code through PolCert's verified code
generator.

The public invocation is:

```text
polopt [optimizer options] input.loop
```

There is one option language and one normalization path. The user does not
select a native mode or a Pluto-compatibility mode. In particular, the final
interface has no `--pluto-compat` flag and no automatic mode switch triggered by
particular options.

The wrapper boundary is deliberately narrower than the complete Pluto command:

- The input is PolCert's `.loop` language. `--pet` and `--readscop` do not change
  the compiler frontend.
- The output is PolCert Loop or ParallelLoop text. Cloog and Pluto C-output
  options do not change the backend.
- The supported optimizer options use Pluto's names and explicit meanings.
- PolCert-specific inspection and theorem-facing options are extensions to the
  same command, not a second option mode.

`polcert` remains the separate entry point for checking an externally supplied
pair of OpenScop schedules. Experimental witness tools should remain separate
commands or explicit `validate-*` actions; they must not influence normal route
selection.

## 2. Default Profile

PolOpt defines one stable checked default profile. It does not inherit
undocumented defaults from whichever Pluto executable happens to be on
`PATH`. The default is:

| Dimension | Default |
| --- | --- |
| schedule | affine scheduling |
| ISS | disabled |
| tiling | one-level rectangular tiling |
| intra-tile rescheduling | disabled |
| diamond tiling | disabled |
| parallel annotation | disabled |
| vector annotation | disabled |
| unroll-jam | disabled |
| fusion policy | smart fusion |
| dependence engine | pinned ISL configuration |

This profile gives `polopt input.loop` a complete checked route. Positive and
negative Pluto options override these defaults. For example,
`--intratileopt` enables the post-tiling affine phase and
`--nointratileopt` explicitly retains the default. The driver never asks users
to spell every negative option merely because the pinned Pluto source has
different internal defaults.

The driver must pass a complete phase-specific option set to Pluto. Pluto's own
defaults therefore cannot silently change PolOpt behavior after a Pluto update.

## 3. Option Semantics

### 3.1 Structural and Scheduling Options

`--iss` enables index-set splitting before scheduling. `--identity` selects the
identity schedule; it does not also disable tiling. Use
`--identity --notile` for identity code generation without tiling.

`--tile` and `--notile` select the tiling boundary. Because tiling is enabled in
the PolOpt default profile, `--tile` is an explicit restatement of the default.
`--identity-tiled` may remain temporarily as an alias for
`--identity --tile`, but it is not a separate route.

### 3.2 Tiling Options

Tiling has three independent properties:

```text
enabled:       false | true
levels:        one | two
shape:         rectangular | diamond
diamond mode:  one-dimensional | full-dimensional concurrent start
intra-tile:    fixed | rescheduled
```

`--second-level-tile` implies tiling unless the user also supplies `--notile`,
which is a contradiction. `--diamond-tile` and `--full-diamond-tile` likewise
require tiling. Full diamond implies diamond. It asks Pluto to search for
full-dimensional concurrent start across the eligible band hyperplanes instead
of enabling concurrent start along one dimension. It is a diamond producer
policy, not a third tile shape or a different validator.

The full-dimensional recipe passes both `--diamond-tile` and
`--full-diamond-tile` to Pluto. This is one phase, not two: Pluto represents
diamond enablement and the full-dimensional search modifier as two independent
option fields. PolOpt's resolved route records the same state once as
`Diamond FullDimensionalStart`.

`--intratileopt` adds a final affine rescheduling after the tiling boundary.
The option applies to rectangular, diamond, identity, ISS, and second-level
routes whenever their candidates pass the existing phase validators.

### 3.3 Parallel and Vector Options

Parallel and vector requests are independent annotations on the same checked
program. They are not alternatives in an `execution_family` sum type.

```text
parallel: disabled | hinted-one | hinted-many
vector:   disabled | hinted-innermost
```

`--parallel` requests a Pluto-hinted parallel dimension. `--multipar` refines
that request to all certifiable hinted dimensions and therefore implies
`--parallel`.

The parallel request has two separately checked effects. Pluto may first create
a tile schedule intended for parallel execution; PolOpt treats that schedule as
an untrusted post-tiling affine candidate. Pluto then reports parallel loop
hints; PolOpt treats those hints as untrusted certificate candidates. Accepting
the schedule does not accept the hint, and accepting a hint does not bypass the
schedule validator.

`--prevector` requests an innermost vector dimension; `--vector` is a PolOpt
alias. Vectorization uses the same doall certificate as parallelization and adds
the structural requirement that the selected loop is innermost.

The current `--parallel-current d` and `--vector-current d` options expose a
padded internal schedule coordinate. They exist for theorem reproduction and
regression tests; the number is neither a source iterator nor a stable loop
depth. They must move to internal validation tooling and are not part of the
artifact-facing compiler interface.

The target semantics must match this contract. A vector loop is an innermost
parallel loop whose iterations may interleave. It is not a sequential loop with
only a printed marker. If a dimension is selected for both parallel and vector
execution, the generated annotation records vector execution for that
dimension; the vector certificate supplies its parallel safety condition.
Other certified outer dimensions remain parallel.

The current v10 implementation does not meet this part of the contract:
`execution_family` makes parallel and vector mutually exclusive, and
`ParallelLoop.PTLoopVec` currently concatenates iteration traces. Both must be
changed before the interface is final.

### 3.4 Post Passes

`--const-unroll` is an independent verified postpass, not a Pluto scheduler
oracle flag and not another spelling of unroll-jam. On ordinary `Loop` output,
it fully expands every loop whose lower and upper bounds are integer constants.
On annotated `ParallelLoop` output, it expands only constant-bound `SeqMode`
loops: `ParMode` and `VecMode` loops retain their mode, origin tag, and bounds,
while nested sequential loops remain eligible. The extracted sequential and
annotated composition endpoints connect the corresponding rewrite to every
verified producer. An explicit request is rejected if the selected output has
no eligible sequential loop.

`--unrolljam` is also a post-code-generation transformation, and `--ufactor n`
supplies its factor unless automatic tile-size selection owns that option. The
sequential path now invokes an extracted actual-domain affine validator before
each sibling-loop fusion. `LoopJamBridge` connects accepted certificates to the
native trace theorem, `LoopJamContext` covers recursive lowering, and
`compile_with_unrolljam_correct` composes the complete returned Loop program
with its selected producer, optional constant unrolling, and cleanup.

Sequential output accepts the complete checked postpass. A narrow parallel
composition is also exposed: run checked unroll-jam on the sequential Loop
result, re-extract the transformed result, and obtain a fresh identity-codegen
parallel certificate. This is a composition of two verified endpoints; it does
not transport an old annotation through the rewrite. It succeeds when the
rewritten bounds remain in the current affine extractor, as demonstrated by
constant-range block unrolling. Symbolic block/remainder bounds commonly
introduce `Div`, `Max`, or `Min`, so those combinations are rejected during
fresh extraction. Vector output remains rejected. Broader support requires a
metadata-preserving annotated unroll-jam theorem or a proved piecewise-affine
re-extraction path.

### 3.5 Oracle-Tuning Options

Fusion objectives, dependence-engine controls, solver controls, and tile-size
model parameters configure Pluto's candidate search. They do not select a
verified compiler theorem by themselves.

Each option has one owning producer phase. For example, a fusion objective
belongs to affine scheduling, while tile-size parameters belong to tiling.
The driver passes an oracle option only to its owning phase. It must not append
one undifferentiated list of extra flags to every Pluto invocation.

Mutually exclusive objective, dependence, and solver selections are rejected
independently of command-line order. Numeric values are parsed and range-checked
before Pluto runs.

### 3.6 Unsupported Options

Known unsupported options receive a stable category and reason:

| Category | Examples | Behavior |
| --- | --- | --- |
| frontend | `--pet`, `--readscop` | reject; `.loop` is the source contract |
| Pluto dump interface | `--dumpscop` | reject; use PolOpt inspection actions |
| foreign backend | `--bee`, `--cloog*`, `--codegen-context` | reject |
| output formatting/path | `--indent`, `-o` | reject until PolOpt implements the same effect |
| unsupported semantic transform | storage privatization without a checked state model | reject |
| stale option | options rejected by the pinned Pluto binary | reject |

An option is marked supported only when PolOpt delivers its user-visible effect.
Passing an option to Pluto while discarding its storage or backend effect is not
support. Disabling an irrelevant foreign-backend feature may be accepted as an
explicit no-op, but the driver reports that decision through `--explain`.

## 4. Internal Representation

The driver uses four representations. No layer may be skipped.

### 4.1 Parsed Request

The parser records option occurrences without choosing a compiler route:

```ocaml
type toggle = Unspecified | Enabled | Disabled

type diamond_concurrent_start = OneDimensional | FullDimensional

type tile_shape =
  | Rectangular
  | Diamond of { concurrent_start : diamond_concurrent_start }

type request = {
  schedule : [ `Affine | `Identity ] option;
  iss : toggle;
  tiling : toggle;
  levels : [ `One | `Two ] option;
  shape : tile_shape option;
  intra_tile : toggle;
  parallel : parallel_request option;
  vector : vector_request option;
  unroll_jam : unroll_request option;
  oracle : oracle_request;
  observation : observation_request;
  input : string;
}
```

The parser does not contain `force_*`, `*_seen`, or `compat_mode` booleans.
It reports syntax errors and records contradictory occurrences for the resolver.

### 4.2 Resolved Request

The resolver applies the PolOpt default profile, expands implications, and
rejects contradictions. It is pure and order-independent. Examples:

- `--identity` resolves to identity plus the default one-level tiling.
- `--identity --notile` resolves to identity without tiling.
- `--multipar` resolves to hinted-many parallel execution.
- `--full-diamond-tile` resolves to diamond tiling with full-dimensional
  concurrent-start search.
- `--notile --intratileopt` is rejected.
- `--parallel --noparallel` is rejected regardless of order.

### 4.3 Checked Compilation Plan

The planner maps the resolved request to an ordered list of semantic phases:

```ocaml
type semantic_phase =
  | IssSplit
  | AffineSchedule
  | Tiling of tiling_spec
  | FinalTileSchedule of final_schedule_spec
  | ParallelAnnotations of parallel_spec
  | VectorAnnotation of vector_spec
  | VerifiedCodegen
  | UnrollJam of unroll_spec
  | Cleanup

type plan = {
  phases : semantic_phase list;
  oracle_calls : oracle_call list;
  theorem_route : theorem_route;
}
```

The representation may group code generation and annotations to match extracted
Coq functions, but the logical plan remains explicit. The planner rejects a
request only when the repository has no sound composition for its phases.

### 4.4 Execution State

The executor passes the plan explicitly. `Scheduler.current_*` global references
must not determine semantics. Every Pluto call receives a complete immutable
`oracle_call` containing its input artifact, expected output artifacts, phase,
and flags.

This makes `--explain`, tests, and actual execution consume the same plan.
`--explain` must not reconstruct a second approximation of the command from raw
booleans.

## 5. Phase and Validation Boundaries

Every normal producer route crosses one extracted top-level compiler boundary:

```text
resolved request -> checked plan -> raw theorem configuration
                 -> extracted compile -> output
```

The `raw theorem configuration` chooses a proved pipeline; it does not bypass
that pipeline or authorize an OCaml implementation of the transformation.
Configuration rejection returns no target. Oracle hints and route selection may
remain untrusted because every successful target is returned by the extracted
`compile` entry point and is covered by its raw-configuration correctness
theorem. A checked postpass is not enough to satisfy this invariant on its own:
it must either be composed under the same final end-to-end theorem or make the
combined request fail before compilation.

The proof route for the generic affine, tiling, final-affine composition is
named `PostTilingAffine`, including for rectangular intra-tile routes. It is not
named after a tile shape. Likewise, the `Diamond` constructor carries a value
named `OneDimensionalStart` or `FullDimensionalStart`; there is no nested
diamond operation. The payload records the scope of Pluto's concurrent-start
search.

For the most complete polyhedral producer route, the plan is:

```text
.loop parse and elaboration
  -> verified extraction
  -> ISS candidate and complete-cut validation, when requested
  -> affine schedule candidate and affine validation
  -> pure tiling candidate and permutable-band validation
  -> final tile schedule and affine validation
     (intra-tile order, diamond rescheduling, and parallel tile scheduling)
  -> parallel and vector certificate selection on the final schedule
  -> verified annotated code generation
  -> checked unroll-jam and cleanup, when requested
  -> output
```

Identity scheduling removes the affine scheduling candidate, but it does not
remove later requested phases. No phase trusts a successful exit code, a Pluto
loop hint, or a previous validator for a different transformation.

Every tiled route records three schedule snapshots: the pre-tiling schedule,
the schedule immediately after strip-mining/tiling, and the final schedule.
The tiling validator receives the first two snapshots. The affine validator
receives the last two when they differ. This uniform boundary also covers the
tile schedule that Pluto creates for `--parallel`; the driver does not hide that
schedule change inside tiling validation. Non-tiled routes record source and
final affine schedules only. Parallel and vector certificates refer to the
final schedule used by code generation.

## 6. Failure Rules

The driver distinguishes three failures:

1. Invalid request: contradictory flags, malformed values, or no verified phase
   composition. Reject before running Pluto and return exit status 2.
2. Producer failure: Pluto cannot produce the requested artifact. Report the
   phase and Pluto invocation, then return exit status 1.
3. Validation failure: a produced candidate fails its owning checker. Emit no
   optimized program and return exit status 1.

The final artifact uses strict behavior for explicitly selected routes. It does
not silently replace a rejected tiled, parallel, vector, or unroll-jam request
with a different optimization. Any future best-effort mode must be explicit and
must report the exact verified fallback route.

Every failure record names:

```text
stage, requested feature, normalized plan, producer result, validator result
```

## 7. Diagnostics

`--explain` prints the resolved request and actual plan, then continues with
normal compilation. `--dry-run` prints the same plan and exits before invoking
Pluto. The output contains:

- resolved defaults and explicit overrides;
- semantic phases in execution order;
- exact Pluto command for each oracle call;
- validator and theorem endpoint for each phase;
- accepted no-op options and rejected unsupported effects.

Normal compilation keeps diagnostics concise. `--silent` suppresses progress
messages but never suppresses errors or validation failures.

## 8. Migration from v10

The migration should proceed in this order:

1. Add parsed and resolved request types with golden normalization tests.
2. Make the default profile explicit and remove every automatic call to
   `enable_pluto_compat`.
3. Remove `--pluto-compat` from the public grammar. The artifact has not frozen
   this interface, so a deprecation mode is unnecessary.
4. Replace `SLoopConfig.config` route booleans with the parsed request.
5. Replace `execution_family` with independent parallel and vector specs.
6. Compile the resolved request into one immutable plan and make
   `--explain` print that plan.
7. Pass immutable oracle calls into `Scheduler`; remove semantic global refs and
   the unscoped `current_pluto_extra_flags` list.
8. Preserve existing extracted theorem routes behind a single
   `theorem_route_of_plan` boundary.
9. Keep the shape-independent `PostTilingAffine` theorem-route names and the
   explicitly named concurrent-start field for diamond producer modes.
10. Change vector target semantics to certified innermost interleaving and add
   combined parallel-plus-vector checked code generation.
11. Generalize checked unroll-jam to annotated output or retain the explicit
    composition rejection until that proof is complete.
12. Move standalone validation tooling out of normal option normalization.
13. Delete the old Python compatibility driver after the native tests cover the
    same option table and plan traces.

## 9. Acceptance Criteria

The interface is final only when all of the following hold:

- `polopt input.loop` reaches the documented default checked plan.
- No option implicitly changes parsing mode.
- Adding `--smartfuse` changes only the affine oracle configuration; it does not
  activate stricter default checks.
- Option order does not change the resolved plan.
- Every positive/negative pair has contradiction tests.
- `--identity` changes only the schedule dimension.
- Intratile routes cover rectangular, diamond, identity, ISS, second-level,
  parallel, and vector plans.
- Parallel and vector can coexist, and vector output has certified innermost
  interleaving semantics.
- Unsupported unroll-jam composition fails before Pluto runs until its checked
  annotated-output pass exists.
- Every accepted oracle option appears only in its owning Pluto call.
- Every accepted semantic option has a visible effect case or a documented
  not-applicable case.
- Every rejected candidate emits no optimized output.
- Every successful producer path returns the result of exactly one extracted
  top-level compiler entry whose theorem covers the complete requested plan.
- `--explain` and execution use the same immutable plan.
- The native option suite no longer invokes `--pluto-compat`.
- Clean proof, extraction, CLI, route, and end-to-end suites pass in the frozen
  artifact image.

## 10. Current v10 Gaps

The v10 route normalization is a useful intermediate step, but it does not yet
implement this contract:

- mode selection remains embedded in option parsing;
- the mutable config mixes syntax, defaults, oracle flags, and compiler routes;
- `--pluto-compat` and automatic mode activation coexist;
- `--identity` still changes tiling indirectly;
- parallel and vector remain mutually exclusive;
- vector target semantics remains sequential;
- unroll-jam cannot compose with annotated output;
- scheduler globals and an unscoped extra-flag list still affect execution;
- some accepted options do not deliver their complete user-visible effect.

These are driver and composition tasks. They do not invalidate the existing
phase validators or end-to-end theorems, but they must be resolved before the
artifact presents `polopt` as a coherent compiler interface.
