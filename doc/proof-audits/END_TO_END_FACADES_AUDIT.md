# Frontend and driver facade audit

> **Resolution on `artifact/verified-compilation-v9-candidate` (2026-08-07).** The endpoint scope
> warning below describes the audited pre-fix snapshot.  The final facade now
> reaches a checked parallel chain whose raw semantics admits arbitrary
> order-preserving interleavings and whose actual execution is justified by the
> validator certificate through codegen-origin and ordered-trace proofs.

## Scope and generated data

Read-only audit of:

- `src/StrengthenDomain.v`
- `driver/PolOpt.v`
- `driver/SBandTilingOptBridge.v`
- `driver/VerifiedParallelCompilerConfig.v`
- `driver/ExtractedPipelineCorrect.v`

Per-file declaration inventories and raw external-reference evidence:

- `/tmp/polcert-strengthendomain-declarations.csv` and `.md`
- `/tmp/polcert-polopt-declarations.csv` and `.md`
- `/tmp/polcert-sbandtilingoptbridge-declarations.csv` and `.md`
- `/tmp/polcert-verifiedparallelcompilerconfig-declarations.csv` and `.md`
- `/tmp/polcert-extractedpipelinecorrect-declarations.csv` and `.md`
- matching `/tmp/*-external-refs.txt` files
- `/tmp/polcert-endtoend-facades-long-proofs.md`

The scanner found 218 declarations/constructors: 30, 73, 28, 79, and 8 in
the file order above.  It strips nested comments/strings, records statement and
proof spans, internal dependencies/callers, and qualified external uses.
`PolOpt` has several ubiquitous alias names (`Core`, `BaseOpt`, `ident`, etc.),
so its raw qualified-use counts are conservative over-approximations; the
classification below is based on inspection of the actual instantiation site,
not those counts alone.  A theorem with no Rocq caller may still be an intended
public endpoint; this matters especially for `ExtractedPipelineCorrect`.

## Executive verdict

These files contain three different kinds of material that should not be read
as one undifferentiated correctness proof:

1. **Real semantic glue.**  `StrengthenDomain` proves that redundant prefix
   constraints preserve instances and well-formedness.  The lower half of
   `PolOpt` composes extraction-facing polyhedral routes, affine validation,
   tiling validation, code generation, fallback, and `State.eq`.
2. **Implementation correspondence.**  `SBandTilingOptBridge` and the bridge
   branches in `ExtractedPipelineCorrect` show that hand-instantiated code used
   by extraction has the same impure behavior as generic code carrying the
   semantic proofs.
3. **Facade enumeration.**  `VerifiedParallelCompilerConfig` and most of
   `ExtractedPipelineCorrect` enumerate supported configuration constructors
   and dispatch to already-proved route theorems.  Their large proofs are
   coverage matrices, not additional compiler-correctness insights.

The current public theorem types can be preserved while making this separation
much clearer.  The highest-value cleanup is local factoring in
`StrengthenDomain`, explicit sectioning/branch labels in the two coverage
files, and removal of proof duplication only where the semantic boundary
remains visible.

## Recommended reader route

1. Read `StrengthenDomain.strengthen_domain` (64-71) and
   `strengthen_pprog` (87-89): the pass adds constraints inferred by summing
   opposite bounds on the current iterator.
2. Read `strengthen_domain_in_poly` (128-141), then
   `instance_list_semantics_unstrengthen` (474-490).  This is the semantic
   reason the frontend may later erase the strengthening step.
3. In `PolOpt`, read only executable definitions 135-194 first:
   checked affine scheduling, accepted tiling, and affine fallback.
4. Follow the matching correctness chain at 353-375, 502-532, 534-633.
   This establishes post-extraction polyhedral refinement route by route.
5. For band/diamond routes, move to the already-proved generic
   `PolOptBandTiling` theorems; use `SBandTilingOptBridge` only to understand why
   the concrete extracted implementation is covered.
6. Read `ExtractedPipelineCorrect.extracted_sequential_compile_correct`
   (72-85) for the actual sequential executable endpoint.
7. Read `VerifiedParallelCompilerConfig.compile_verified` (174-240) and the
   concise theorem statement at 372-377, then inspect
   `ExtractedPipelineCorrect.extracted_parallel_compile_correct` (250-263) for
   the actual concrete endpoint.
8. Finally read `ParallelLoop.PTLoopPar` (273-277) before interpreting the
   word “parallel” in the endpoint: the semantic relation itself requires an
   `interleave_safe` premise.

## `StrengthenDomain.v`

### Ownership and theorem chain

This module owns one coherent pass: add redundant prefix-only constraints to a
polyhedral domain without changing the represented instances.

Semantic chain:

```text
original constraint and domain membership
 -> every inferred guard is satisfied
 -> strengthened and original in_poly tests are equal
 -> belongs_to is unchanged per PolyInstr
 -> flatten_instrs is unchanged for the mapped program
 -> poly_instance_list_semantics transports back
 -> instance_list_semantics transports back
```

Well-formedness chain:

```text
all inferred constraints keep the original column width
 -> strengthened PolyInstr is wf
 -> strengthened pprog is wf / wf_affine
```

The externally important declarations are `strengthen_pprog` (used throughout
sequential, band, parallel, and syntax drivers),
`strengthen_pprog_wf_affine`, and
`instance_list_semantics_unstrengthen`.  `strengthen_pprog_wf` is a sensible
general public theorem despite having no current caller.

### Misplaced, duplicate, and unused declarations

- `add_vector_length_same`, `exact_listzzs_cols_app`, and
  `exact_listzzs_cols_implies_poly_nrl_le` are generic linear-algebra/list facts.
  The latter two are independently re-proved in `PrepareCodegen.v`.  Their
  canonical owner should be `Linalg.v`, beside `exact_listzzs_cols`; preserve
  the current names as forwarding lemmas.
- `add_constraint_exact_cols` has no caller; the live proof calls
  `add_vector_length_same` directly.
- `env_dim_of` and `strengthen_prefix_len` have no real caller in this module
  or through the qualified module path.  The `env_dim_of` hits in
  `ParallelValidator` are a different local definition.
- `strengthen_pprog_wf` is unused, but is not dead in the same sense: it is the
  natural non-affine counterpart of the live affine theorem.

### Readability work

P0: factor the mirrored membership proof in
`flatten_instrs_strengthen_iff`; factor reconstruction of `wf_pinstr` while
keeping its field obligations explicit.  P1: move the three generic column
lemmas to a shared owner with forwarding wrappers.  P2: annotate the unused
compatibility/general declarations rather than deleting public names.

## `PolOpt.v`

### What the file actually owns

The upper half is executable orchestration.  It imports an affine candidate,
checks it, optionally imports and checks a tiled candidate, optionally applies
ISS, and otherwise falls back to a previously verified route.  The semantic
heart is the following small set:

- `scheduler'_correct`: accepted affine schedule refines the input program.
- `checked_tiling_current_view_prepared_codegen_correct`: current-view codegen
  after successful tiling validation refines the pre-tiling program.
- `affine_opt_prepared_from_poly_correct`: affine validation plus codegen.
- `try_tiling_prepared_from_phase_correct`: accepted tiling or verified
  codegen fallback.
- `try_phase_pipeline_from_source_pol_correct`: affine midpoint plus tiling,
  with affine fallback for failed external/import/check steps.
- `identity_tiling_generic_opt_prepared_from_poly_correct`: outer route
  selection for the identity-tiling pipeline.

These are genuine semantic composition proofs.  In particular,
`try_phase_pipeline_from_source_pol_correct` composes two output-to-source
`State.eq` facts in the correct order; failures do not need a semantic theorem
about the failed candidate because the executable path returns a separately
verified fallback.

This file does **not** by itself close every Loop-to-Loop route.  The reusable
extractor/strengthening closure and final `Opt*` theorems are primarily in
`PolOptCorrect.v` and `PolOptBandTiling.v`.

### Wrappers and compatibility surface

- `scheduler'`, `affine_opt_prepared_from_poly`, `phase_opt_*`, `Opt*`, and the
  aliases at 486-500 preserve historical/public naming layers.
- `checked_tiling_validate_correct` is a one-line public forwarding theorem.
- `Extract_Schedule_correct`, `extractor_success_wf_pprog`, and
  `Extract_Schedule_Prepared_correct` have no repository caller.  They are old
  direct-path theorems superseded by the prepared/facade chain.
- `phase_scop_scheduler`, `to_tiling_pprog`,
  `check_wf_polyprog_correct`, and `EqDom` have no verified qualified caller;
  they appear to be compatibility exports.
- The file-global `apply_total`, `apply_partial`, `apply_partial_res`, and their
  three notations have no operator use in the current repository.  `print`,
  `time`, and `print_CompCertC_stmt` are extraction/runtime hooks rather than
  semantic glue.

### Readability work

P0: divide the file into executable orchestration, route correctness, and
compatibility exports.  Introduce a small private lemma for the three identical
“codegen `pol_mid` then reflexive equality” branches in
`try_tiling_prepared_from_phase_correct`.  Keep the affine/tiling composition
explicit.  P1: document compatibility aliases and old theorem roots.  Moving
the correctness block to another file would disturb existing qualified theorem
paths and dependency direction, so it is not a safe first cleanup.

## `SBandTilingOptBridge.v`

### Exact role

This file proves `impeq` between two implementations of the same dispatch
logic: `SBandTilingOpt`, whose stable concrete names are extracted, and
`SBandTilingOptShared.BandGeneric`, whose functor instance carries semantic
proofs.  `impeq` is compatible with `mayReturn`, so these theorems let the
concrete execution hypothesis be rewritten before applying a generic
correctness theorem.

It does not prove affine scheduling, tiling, ISS, diamond tiling, or codegen
correctness.  Those properties enter only after the bridge rewrite.

The six live public endpoints are:

```text
opt_impeq_generic
opt_with_iss_impeq_generic
opt_identity_tiled_impeq_generic
opt_identity_tiled_with_iss_impeq_generic
opt_diamond_impeq_generic
opt_diamond_with_iss_impeq_generic
```

All are consumed by `ExtractedPipelineCorrect`.  The internal chain mirrors
each nested dispatcher down to reflexive leaves.

`prepared_codegen_after_tiling_route_impeq`,
`reject_post_tiling_affine_impeq_generic`, and the three final `*_prepared_*`
corollaries have no caller.  Preserve them as compatibility wrappers if public
visibility must remain unchanged.

### Readability work

P0: add section headers for ordinary tiling, identity tiling, ISS, diamond, and
final endpoints; label stages inside the 36-line diamond bridge.  P1: use short
local names for the repeated generic importer/validator path.  Do not hide the
branch coverage behind a broad tactic.

## `VerifiedParallelCompilerConfig.v`

### Structure and reachability

The module defines 32 raw constructors (31 supported plus `RawUnsupported`)
and 31 verified constructors.  `check_config` is an enumeration check: outside
the nested sequential config it accepts every named route and rejects only
`RawUnsupported`.  It is not the affine/tiling/doall validator.

`compile_verified` dispatches one sequential route, ten single parallel-current
routes, ten vector-current routes, and ten multi-parallel-current routes.
`compile_verified_correct` is the exact proof-side coverage matrix.
`compile_correct` adds only `check_config`; `compile_unsupported_no_result`
records the rejected constructor.

There is no direct Rocq instantiation/use of this generic functor elsewhere in
the current tree.  It remains an intended theorem-facing facade and is named by
the artifact report.  The executable facade is separately hand-written in
`syntax/SVerifiedParallelCompilerConfig.v`, and its actual correctness is proved
again in `ExtractedPipelineCorrect.v`.

`checked_sequential_current_annotated_codegen` and its correctness theorem are
not on the live compile path.  The two `finish_strengthened_source*` Ltacs at
308-347 are also unused remnants.  `opt_parallel_current_identity_tiled_correct`
is a one-line alias used only by the local dispatcher proof.

### Sequential lifting

The sequential subcompiler produces `Loop`; `checked_lift_sequential_loop`
tags it as a `ParallelLoop` and checks `all_es_safeb`.  Its theorem uses
`ParallelLoop.semantics_refines_erased`, erases the tags, and then composes with
the sequential compiler theorem.  This is genuine adapter semantics, distinct
from parallel certification.

### Exact endpoint contract

`compile_correct` proves:

```text
compile cfg loop may return pl
and pl has a ParallelLoop.semantics execution st -> st'
-------------------------------------------------------
there is a source Loop execution st -> st''
with State.eq st' st''
```

It is successful-output soundness and final-state refinement.  It does not
prove that compilation returns, never rejects, preserves divergence, or that
every source execution has a target execution.

For a `ParMode` loop, `ParallelLoop.PTLoopPar` itself requires
`interleave_safe`.  Therefore this endpoint covers executions already admitted
by the safe-interleaving target semantics.  It does not, by this theorem alone,
derive arbitrary backend interleaving safety from the doall validator
certificate.  The existing certificate-to-generated-loop and unrestricted
backend-semantics gaps must remain separate from readability cleanup.

### Readability work

P0: state the endpoint contract and the meaning of `check_config` in comments;
group the four constructor families in both dispatcher and proof.  P1: quarantine
the unused codegen helper/Ltacs as compatibility remnants without removing
visible names.  The explicit 31-case correctness proof should remain explicit.

## `ExtractedPipelineCorrect.v`

### Exact role and roots

This file is the final connection to the concrete `S*` modules used by
extraction.  It has no downstream Rocq caller because its correctness theorems
are roots; `tools/artifact/proof_report.py` names them explicitly.

- `extracted_sequential_compile_verified_correct` covers all 13 supported
  sequential constructors.  Several facade names select the same underlying
  band route, so 13 cases do not mean 13 different semantic arguments.
- `extracted_sequential_compile_correct` is the actual raw sequential endpoint.
- `extracted_checked_lift_sequential_loop_correct` and
  `extracted_parallel_compile_seq_verified_correct` lift the concrete
  sequential compiler into the annotated target.
- `extracted_parallel_compile_verified_correct` covers the 31-constructor
  unified facade via concrete/generic bridges.
- `extracted_parallel_compile_correct` is the actual raw unified endpoint.
- The two unsupported theorems prove explicit rejection of the sentinel
  configurations.

The sequential endpoint has `Loop.semantics` on both source and target.  The
unified endpoint has source `Loop.semantics` and target
`ParallelLoop.semantics`.  Both are conditional on successful `mayReturn` and
prove an existential source result related by `State.eq`.

### Readability work

P0: promote the two raw `*_compile_correct` statements in the proof map and
state their exact target languages.  Add constructor-family comments to the
96-line parallel coverage proof.  Keep the bridge-plus-correctness pair on
adjacent lines.  The duplicated concrete/generic sequential-lift proof is only
22 lines and is safer to retain than to introduce a new config conversion and
large facade bridge solely to remove it.

## Refactoring order under unchanged public interfaces

### P0: clarity with minimal proof risk

1. Add file sections and exact endpoint comments.
2. Label constructor families in both exhaustive correctness proofs.
3. Factor `StrengthenDomain.flatten_instrs_strengthen_iff` through one private
   membership-transport lemma.
4. Factor the unchanged-field reconstruction in
   `strengthen_pi_wf_pinstr`.
5. Factor only the repeated reflexive fallback leaf in
   `try_tiling_prepared_from_phase_correct`.

### P1: ownership cleanup with forwarding names

1. Move shared exact-column lemmas from `StrengthenDomain` and
   `PrepareCodegen` to a canonical utility owner; leave theorem aliases at both
   old paths.
2. Mark old `PolOpt` theorems and facade aliases as compatibility surfaces.
3. Organize `SBandTilingOptBridge` by route family and retain the six live
   bridge endpoints unchanged.

### P2: larger design work, not a readability prerequisite

1. Generate generic and extracted config dispatchers from one route table.
2. Replace hand-instantiated/generic duplication with a principled extraction
   naming mechanism.
3. Close the independent parallel certificate-to-unrestricted-execution and
   dimension-correspondence obligations before strengthening paper claims.

## Bottom line for paper-facing claims

The strongest concrete sequential statement in this group is
`extracted_sequential_compile_correct`: any admitted execution of a successfully
returned transformed structured loop corresponds, up to `State.eq`, to an
execution of the source structured loop.

The strongest concrete unified statement is
`extracted_parallel_compile_correct`, with the same refinement shape into
`ParallelLoop.semantics`.  Because that semantics embeds safe-interleaving
evidence in `PTLoopPar`, the theorem should be described as correctness for the
formal annotated-loop semantics, not yet as a theorem for every arbitrary
runtime/backend interleaving.



---

# End-to-end frontend/facade long-proof audit

Scope: current `proof/readability-cleanup` worktree.  Proof-body counts exclude
`Proof.` and the closing command.  This file covers every proof with at least
30 body lines in the requested five files.  Near-threshold proofs that carry
important semantic glue are listed separately at the end.

## `src/StrengthenDomain.v`

### `strengthen_pi_wf_pinstr` (269-316; 42 body lines)

**Obligation.**  Extending a polyhedral instruction domain with inferred
prefix constraints preserves `wf_pinstr`.

**Actual proof.**  The proof unfolds `wf_pinstr`, destructs its deeply nested
conjunction, proves exact column width for the strengthened domain, and then
reassembles the same conjunction.  Only the domain-column and derived
`poly_nrl` obligations change; schedule, transformation, access transformation,
and read/write access obligations are copied unchanged.

**Complexity judgment.**  The underlying argument is small.  Most length is an
artifact of the conjunction representation of well-formedness and the
five-argument eliminator shape of `exact_listzzs_cols`.

**Readability-preserving cleanup.**  Add a private lemma saying that replacing
`pi_poly` by an exact-width domain preserves all other `wf_pinstr` fields, then
instantiate it with `inferred_prefix_guards_exact_cols`.  Keep the current
theorem name and type as the public wrapper.  Avoid broader automation here:
the current explicit list of preserved fields is useful as a representation
audit.

### `flatten_instrs_strengthen_iff` (389-449; 54 body lines)

**Obligation.**  Mapping `strengthen_pi` over the instruction list leaves the
flattened instruction-instance list relation unchanged.

**Actual proof.**  Both directions preserve prefix, `NoDup`, and sorting
evidence, while translating the existential `nth_error` witness with
`nth_error_strengthen_pprog(_inv)` and translating membership with
`strengthen_pi_belongs_to_iff`.

**Complexity judgment.**  Semantically important but proof-theoretically
routine.  Lines 400-421 and 425-447 are nearly mirror images.

**Readability-preserving cleanup.**  Introduce a private pointwise witness
lemma for the membership component of `flatten_instrs`, in both directions,
and rebuild the unchanged structural conjuncts once.  A more reusable version
belongs in `PolyLang`: mapping instructions with a pointwise `belongs_to`
equivalence preserves `flatten_instrs`.  If moved, retain this theorem as a
forwarding specialization so its public path and type remain unchanged.

## `driver/SBandTilingOptBridge.v`

### `try_verified_diamond_after_phase_mid_band_impeq_generic` (98-142; 36 body lines)

**Obligation.**  The hand-instantiated extracted diamond route and the proved
generic functor route are `impeq`.

**Actual proof.**  It mirrors the executable decision tree: infer tiling
witness, import post-tile program, observe validation route, check post-tile
well-formedness, import the final schedule, validate it, check final
well-formedness, and otherwise take the same rejection branch.  Every leaf is
reflexive `impeq`; `bind_eq_compat` transports equality through impure binds.

**Complexity judgment.**  No tiling semantic argument occurs here.  Length is
entirely caused by nested branch correspondence between duplicated generic and
concrete implementations.

**Readability-preserving cleanup.**  Preserve the explicit branch structure,
but label the success/failure stages with comments and use short local module
aliases for the importer/validator.  A large custom tactic would shorten the
file while making this implementation-coverage audit harder to inspect.  The
larger structural fix is to generate the concrete facade from the generic
route; that is higher risk because stable extraction names motivated the
duplication.

## `driver/VerifiedParallelCompilerConfig.v`

### `compile_verified_correct` (372-415; 36 body lines)

**Obligation.**  Each of the 31 supported verified configuration constructors
selects a route whose admitted `ParallelLoop` execution refines an execution
of the source `Loop` program up to `State.eq`.

**Actual proof.**  Destruct the configuration and invoke one route theorem per
constructor: one sequential lifting theorem, ten single parallel-current
routes, ten vector-current routes, and ten multi-parallel-current routes.

**Complexity judgment.**  This is an exhaustive coverage table, not a complex
proof.  The explicit branches are valuable because adding a constructor forces
this theorem to be revisited.

**Readability-preserving cleanup.**  Keep the explicit proof.  Add comments
before the sequential, single-parallel, vector, and multi-parallel branch
groups, and keep constructor order synchronized with `compile_verified`.
Compressing it with `first [eapply ...]` or broad automation would obscure
which public route theorem discharges each case.

## `driver/ExtractedPipelineCorrect.v`

### `extracted_parallel_compile_verified_correct` (144-248; 96 body lines)

**Obligation.**  The actual hand-instantiated module sent to extraction has the
same end-to-end correctness coverage as the generic proof modules.

**Actual proof.**  The sequential constructor uses the concrete sequential
endpoint plus the checked lift.  Each of the remaining 30 constructors first
rewrites the concrete execution with an `SParallelPolOptBridge` `impeq` theorem
and then applies the corresponding `ParallelPolOptCorrect` theorem.

**Complexity judgment.**  This is the real concrete executable-to-proof
connection, but its length is mechanical route enumeration.  It proves no new
transformation property locally.

**Readability-preserving cleanup.**  Retain the explicit constructor coverage.
Add four group comments and align every bridge theorem beside its correctness
theorem.  Do not replace the list with aggressive automation: this theorem is
the most direct audit that every extracted constructor has both an execution
bridge and a semantic theorem.  A future table-generated facade could remove
the source duplication, but it would be a design change rather than a proof
cleanup.

## Semantically central near-threshold proofs

- `PolOpt.try_tiling_prepared_from_phase_correct` (557-594; 29 body lines):
  accepted tiling composes tiling validation with current-view code generation;
  every failure branch code-generates `pol_mid` and uses reflexive `State.eq`.
- `PolOpt.try_phase_pipeline_from_source_pol_correct` (596-633; 27 body lines):
  composes affine validation, tiling correctness, and `State.eq_trans`; phase,
  import, or validation failure falls back to the affine-only route.
- `SBandTilingOptBridge.try_verified_tiling_after_phase_mid_band_impeq_generic`
  (60-96; 28 body lines): ordinary tiling counterpart of the diamond bridge.
- `ExtractedPipelineCorrect.extracted_sequential_compile_verified_correct`
  (34-70; 28 body lines): exhaustive bridge for the 13 sequential
  configuration constructors.
