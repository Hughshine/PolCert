# Proof Reading Guide

This guide is for a reader who knows Rocq and compiler correctness but has not
recently worked on PolCert. It explains what each proof layer establishes, how
the layers compose, and which declarations carry the main argument. It follows
the proof state tagged `state-eq-polyhedral-verification-complete-2026-07-24-v8`
at commit `0661fe0aa121deaa6ca714f258b96906a1dc0ca8`.

The cleanup branch preserves the exported declarations of the proof modules.
Comments, sections, and proof-only tactics may change, but callers see the same
definitions and theorem names.

## 1. Start from the Contract

The final theorem is
`VerifiedParallelCompilerConfig.compile_correct` in
`driver/VerifiedParallelCompilerConfig.v`. Its semantic direction is:

```text
compile cfg source may return target
target executes from st to st_target
------------------------------------------------
source executes from st to some st_source
State.eq st_target st_source
```

This is the common shape of the component theorems. A validator may reject a
proposal or raise an alarm. If a checked route returns a target and that target
executes, the theorem reconstructs a source execution whose final state is
related by the abstract `State.eq` supplied by the instruction semantics.

Read the final file in this order:

1. `compile_correct` removes the raw-configuration check.
2. `compile_verified_correct` dispatches to one theorem per verified route.
3. `compile_seq_verified_correct` embeds a sequential loop result in the
   common parallel-loop target language.
4. `finish_strengthened_source` shows the recurring end-to-end composition:
   undo strengthening, invoke `Extractor.extractor_correct`, then compose the
   two `State.eq` facts.

The long constructor lists in this file are coverage plumbing. The semantic
content resides in the component theorems described below.

## 2. The Semantic Spine

The proof can be read as one chain:

```text
bounded structured loops
  -- verified extraction --> polyhedral instances
  -- checked ISS ---------> partitioned statement instances
  -- checked schedules ---> reordered fixed instances
  -- checked tiling ------> instances with tile coordinates
  -- checked annotations -> sequential, parallel, or vector loop modes
  -- verified codegen ----> structured target loops
```

Each arrow proves the same backward semantic statement. The driver composes the
arrows with transitivity of `State.eq`. A route that omits an optimization uses
an identity or shorter chain; it does not require a separate semantic model.

Two ideas recur throughout the development:

- **Representation correspondence.** The proof relates source and target
  instruction points, including their statement number, coordinates,
  instruction, access functions, and schedule.
- **Safe reordering.** If the target order reverses two source-ordered points,
  those points must commute. Bernstein-style noninterference turns absence of
  write/write, write/read, and read/write collisions into commutativity.

Affine scheduling changes only the second item. ISS and tiling also change how
statement instances are represented, so they need an additional
correspondence proof.

## 3. Extraction: Loops to Polyhedral Instances

Primary file: `src/Extractor.v`.

The extractor accepts the bounded affine fragment of the structured loop
language. It converts expressions to affine rows, accumulates loop and guard
constraints into statement domains, records affine accesses, and builds the
initial lexicographic schedule.

The proof has four layers:

1. `expr_to_aff_correct` and the test/constraint lemmas connect affine syntax
   to evaluation in a concrete iterator environment.
2. `extract_stmt` and its success-inversion lemmas expose the generated
   statements for instructions, sequences, loops, and guards.
3. The flattening and splitting lemmas relate a sorted list of polyhedral
   instances to the syntax-directed execution of each source construct.
4. `extract_stmt_to_loop_semantics_core_sched` performs the structural proof;
   `extractor_correct` packages it at the program level.

The difficult part is sequencing. Polyhedral semantics flattens all statement
instances and sorts them by timestamp, while loop semantics executes syntax
recursively. For a source sequence, the proof partitions the sorted instance
list by statement number, executes the head, rebases the tail statement
numbers, and executes the tail. For a loop, it partitions by the current
iterator value and applies the induction hypothesis to each iteration.

Recommended reading path:

```text
expr_to_aff_correct
extract_stmt_*_success_inv
extract_stmts_cons_semantics_split_by_nth
core_sched_stmt_stmts_constrs_prefix_mutual
extract_stmt_to_loop_semantics_core_sched
extractor_correct
```

Most list-index and prefix lemmas support one of the two partitioning steps.
Read them on demand from the main structural proof.

## 4. ISS: One Statement to a Domain Partition

Primary files:

- `src/ISSRefinement.v`
- `src/ISSBoolChecker.v`
- `src/ISSCutSemantics.v`
- `src/ISSValidatorCorrect.v`

Index-set splitting (ISS) replaces a source statement with children whose
domains partition the source domain. The children keep the source statement's
instruction, schedule, point witness, transformations, and accesses. Only the
domain and the statement identity change.

`ISSRefinement.v` defines the declarative certificate. For each child, a
witness identifies its parent and assigns one side of every affine cut. The
central obligations establish:

- the child payload matches its parent except for the domain;
- the child domain is the parent domain conjoined with its signed cuts;
- each expected sign vector occurs exactly once for its parent;
- child domains cover the parent domain and are pairwise disjoint.

`ISSBoolChecker.v` turns those obligations into booleans and proves soundness.
`check_domain_partition_complete_cut_shapeb_sound` is the main checker theorem.

`ISSCutSemantics.v` supplies the semantic step. It maps every child instance to
the corresponding parent instance. Coverage supplies a parent for every
source point; disjointness prevents duplicate children for the same source
point; payload equality preserves instruction semantics and timestamps. The
main theorems are `iss_complete_cut_shape_to_before_poly_correct` and
`iss_complete_cut_shape_to_before_correct`.

The public composition theorem is only a few lines:

```text
checked_iss_complete_cut_shape_validate_semantics_correct
  = boolean-checker soundness
  + ISS semantic refinement
```

Read the declarative predicates before the boolean recursion. This makes the
checker appear as executable evidence for a known partition argument rather
than as the definition of ISS correctness.

## 5. Affine Scheduling: Reordering Fixed Instances

Primary file: `src/AffineValidator.v`.

The affine validator compares programs with the same statement domains and
instance coordinates but different schedules. `EqDom` records that fixed-space
correspondence. `compose_ip_ext` pairs the old and new views of an instance so
the proof can discuss both timestamps without losing its instruction and
access information.

For every ordered statement pair, `validate_two_instrs` asks whether a
source-ordered pair can be reversed by the target schedule and still have a
write/write, write/read, or read/write collision. Each question is reduced to
polyhedral emptiness. The proof then follows this chain:

```text
successful emptiness checks
  -> no conflicting access for each reversed pair
  -> the pair is Permutable_ext
  -> sorting by the new schedule preserves list semantics
  -> validate_correct / validate_tiling_correct
```

The main reading checkpoints are:

```text
validate_two_accesses_helper_correct
validate_two_instrs_implies_no_write_collision
validate_pinstrs_ext_implies_permutability
validate_implies_permutability
permutable_instance_lists_preserve_semantics
validate_correct
```

The later `*_integer` definitions repeat the guarded collision kernel with
integer-feasibility checks. They are not a second semantic argument.

The direct tiling validator imports this collision kernel, especially
`validate_two_instrs_under_guards`. It does not call the whole affine schedule
validator to justify a tiled schedule.

## 6. Tiling: Representation and Reordering

Tiling is split between a general semantic relation and executable direct
validators.

### 6.1 General tiling semantics

Primary file: `src/TilingRelation.v`.

A tiling witness says how added tile coordinates relate to the original point
coordinates. Because the target has a different point space, schedule
permutability alone is insufficient. The proof introduces an intermediate
program, `retiled_old`:

```text
after
  -- reorder in the tiled point space --> retiled_old
  -- erase the tile representation ----> before
```

The first step keeps the target's represented instances but orders them by the
lifted source schedule. `tiling_after_to_retiled_old_poly_correct` needs the
reordering-safety premise: every target reversal is a permutable pair.

The second step proves that tiled coordinates represent source points exactly
once and preserve instruction execution. The key source-based theorem is
`tiling_retiled_old_to_before_instance_correct_source`.

`tiling_after_to_before_instance_correct_via_retiled_old` composes the two
steps. This theorem is deliberately independent of how a validator proves the
reordering-safety premise.

Recommended reading path:

```text
tiling_rel_pinstr_structure_source
retiled_old_pinstr
before_of_retiled_old_point_source
tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective
flatten_instrs_after_implies_tiling_ext_exists
tiling_after_to_retiled_old_poly_correct
tiling_retiled_old_to_before_instance_correct_source
tiling_after_to_before_instance_correct_via_retiled_old
```

### 6.2 Direct permutable-band validation

Primary files:

- `src/TilingBandScheduleValidator.v`
- `src/TilingBandMixedSecondValidator.v`
- `src/TilingBandPhaseScalarValidator.v`
- `src/TilingBandDirectRuntime.v`

The direct validator proves the reordering-safety premise through a semantic
permutable-band property. For each selected band component and each ordered
statement pair, it searches for a bad pair satisfying all of these conditions:

```text
the source schedule orders tau1 before tau2
the timestamps agree before the selected band
the selected band component decreases from tau1 to tau2
the pair has a WW, WR, or RW conflict
```

Certified emptiness of every bad-pair region implies that any such decreasing
pair commutes. The core semantic predicate is
`pinstr_list_semantic_componentwise_permutable`.

A second proof, called a reversal bridge in the source, connects a recognized
tiled schedule layout to that property. It shows that every target reversal
must expose a decrease in one checked component. The short central composition
is `semantic_componentwise_permutable_implies_reordering_safe`:

```text
component checker soundness + layout reversal bridge
  -> pprog_tiling_reordering_safe
```

The layout proof is where the tiling variants differ:

- `CommonBandInfrastructure` and `CommonBandDirectChecker` handle ordinary
  strip mining and uniform grouped or interleaved second-level layouts.
- `ProgramWideSemanticReconstruction` handles source-like identity,
  mixed-width, and mixed-depth schedules by reconstructing global schedule
  slots and proving that omitted slots evaluate to zero.
- `ScalarAwareBands` admits fixed scalar schedule rows around loop components.
- `PhaseAwareSemanticBands` separates statements by constant phase prefixes
  and covers phase-separated ordinary and mixed second-level layouts.
- `TilingBandMixedSecondValidator.v` and
  `TilingBandPhaseScalarValidator.v` package the specialized bridges used by
  the runtime dispatcher.

For each bridge, read the proof in five stages: invert the recognized shape;
recover the two statement witnesses; express old and target timestamps; rule
out a componentwise monotone reversal; return the decreasing component needed
by the band property. The long bridge proofs are mostly list-position and
padding arithmetic supporting those five steps.

`checked_tiling_sourceb_complete_direct_band_check_correct` in
`TilingBandDirectRuntime.v` is the runtime-facing theorem. It dispatches among
the proved layout classes. A failed recognizer or failed band check rejects the
candidate; there is no affine-validation fallback for the tiling boundary.

## 7. Parallel and Vector Annotations

Primary files:

- `src/ParallelValidator.v`
- `src/ParallelCodegen.v`
- `driver/ParallelPolOptCorrect.v`

`parallel_safe_dim pp d` states the doall property for one current loop
dimension. Two instances are in the same parallel slice when they have the
same parameter environment and the same current coordinates before `d`, but
different coordinates at `d`. The property requires every such pair to
commute.

`check_pprog_parallel_currentb` reduces this property to an affine validation
query between two synthetic schedule views: one orders only by coordinate `d`,
and the other orders by the prefix before `d`. Its soundness theorem is
`check_pprog_parallel_currentb_sound`; `checked_parallelize_current_sound`
packages the resulting certificate.

`ParallelCodegen.v` attaches sequential, parallel, or vector modes to generated
loops. The semantic proof erases those annotations to the already verified
sequential loop and uses trace-safety to relate annotated execution to erased
execution. The endpoints are:

```text
checked_annotated_codegen_correct_general
checked_vector_annotated_codegen_correct_general
checked_annotated_codegen_many_correct_general
```

Vectorization reuses the doall certificate. Its separate codegen theorem
checks the vector annotation and target trace discipline; it does not require
a separate dependence theory.

`ParallelPolOptCorrect.v` composes preprocessing routes with these annotation
and codegen theorems. The local `finish_checked_*` tactics only remove repeated
proof scripts. Their semantic content is: prove the prepared program is well
formed, obtain correctness of annotation/codegen, obtain correctness of the
preparation route, and compose `State.eq`.

## 8. What to Read and What to Skim

For a first complete pass, read these declarations in order:

```text
Extractor.extractor_correct
ISSValidatorCorrect.checked_iss_complete_cut_shape_validate_semantics_correct
AffineValidator.validate_correct
TilingRelation.tiling_after_to_before_instance_correct_via_retiled_old
TilingBandScheduleValidator.semantic_componentwise_permutable_implies_reordering_safe
TilingBandDirectRuntime.checked_tiling_sourceb_complete_direct_band_check_correct
ParallelValidator.checked_parallelize_current_sound
ParallelCodegen.checked_annotated_codegen_correct_general
ParallelPolOptCorrect.Opt_parallel_current_correct
VerifiedParallelCompilerConfig.compile_correct
```

Then descend into the component whose premise is least clear. In particular:

- Read the extractor's mutual structural proof to understand the frontend.
- Read one ordinary and one second-level reversal bridge to understand tiling.
- Read `validate_two_instrs_implies_no_write_collision` to understand the
  shared dependence kernel.
- Skim the many route-specific `Opt_*_correct` wrappers after checking one
  example; they instantiate the same composition argument.

## 9. Maintenance Invariants

Future proof cleanup should preserve these boundaries:

1. Boolean checker soundness is separate from semantic correctness.
2. Tiling shape recognition is separate from the semantic band property.
3. The direct tiling route may reuse guarded affine collision checks but must
   not silently invoke the whole affine validator as a fallback.
4. Representation-changing transformations must prove point correspondence in
   addition to reordering safety.
5. Route wrappers should compose named component theorems through `State.eq`;
   they should not duplicate component arguments.
6. Refactoring must compare exported module signatures and rebuild downstream
   dependencies, because Rocq dependency fingerprints change even when theorem
   statements do not.
