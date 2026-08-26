# PolCert proof-readability audit: cross-file consolidation

> **Resolution on `artifact/verified-compilation-v9-candidate` (2026-08-07).** The parallel P0 in
> this historical plan has been implemented: unrestricted target interleavings,
> pointwise schedule-coordinate certificates, generated-trace origin, actual
> ordered proof companions, and cleanup reflection are connected through the
> checked driver.  The remaining items in this document are refactoring advice,
> not an open parallel soundness claim.

## 1. Scope, evidence, and interpretation

This document consolidates the completed read-only audits under `/tmp` for:

- `Extractor.v`, `PolyLang.v`, `PolyBase.v`, and `AffineValidator.v`;
- `TilingRelation.v`, `TilingBoolChecker.v`,
  `TilingBandScheduleValidator.v`, and
  `TilingBandMixedSecondValidator.v`;
- `ISSRefinement.v`, `ISSSemantics.v`, and `ISSCutSemantics.v`;
- `ParallelValidator.v`, `ParallelCodegen.v`, and `ParallelLoop.v`;
- `PolOptCorrect.v`, `PolOptBandTiling.v`, and
  `ParallelPolOptCorrect.v`.

These inventories cover 2,694 declarations and approximately 347 long proofs.
The exact long-proof threshold differs slightly among audit scripts: some count
the proof body, while others count inclusive `Proof`--`Qed` span. Each source
audit records its own convention.

All reachability results are repository-local. Most declarations are exported
from functors; lack of a repository caller is not permission to remove a path.
The default policy throughout this plan is:

1. create one canonical implementation in the dependency-lowest appropriate
   owner;
2. retain every old executable definition, theorem statement, notation, and
   qualified module path as an exact definition/theorem wrapper;
3. delete or make a declaration `Local` only after an explicit external-API
   decision.

The working tree changed during the sequence of audits, notably in
`Extractor.v`. Declaration names are the stable consolidation key; line numbers
belong to the snapshots recorded by the individual audit artifacts.

## 2. Consolidated decisions

### P0 correctness boundaries

#### C1. Close or explicitly limit the parallel certificate-to-semantics claim

This is the only confirmed cross-file semantic gap.

`ParallelValidator.checked_parallelize_current_sound` proves
`parallel_cert_sound`, hence pairwise `parallel_safe_dim`. The proof is
substantial and valid. However, `ParallelCodegen` uses only `certified_dim`.
Neither its public correctness theorem nor the driver proof consumes
`parallel_cert_sound`.

`ParallelLoop.PTLoopPar` accepts only an execution already carrying an
`interleave_safe` proof. Therefore the existing endpoint proves that an
already-safe interleaving refines sequential execution; it does not prove that
the validator certificate makes an arbitrary backend/scheduler interleaving
safe. `interleave_family` and `family_ordered_permutable` appear to be the
unfinished beginning of the required bridge.

Required theorem chain before claiming verified parallel execution:

1. prove `family_ordered_permutable trs -> interleave_family trs tr ->
   interleave_safe trs tr`;
2. expose an operational/backend trace premise as `interleave_family`, rather
   than assuming `interleave_safe` in the execution constructor, or prove that
   every backend trace has this family property;
3. use code-generation origin information plus `parallel_cert_sound` to prove
   `family_ordered_permutable` for traces from distinct certified iterations;
4. invoke `checked_parallelize_current_sound` in the driver endpoint and derive
   the safety premise used by erasure refinement.

Step 3 is the real proof obligation. Keep all existing theorems unchanged and
add a stronger, separately named endpoint. Until it exists, paper/API language
must say “safe-interleaving semantics”, not unrestricted parallel execution.

The formal semantics also executes nested modes sequentially inside an outer
`PTLoopPar`, so current proofs do not cover a backend that concurrently executes
several nested parallel annotations. Treat that as an explicit scope limit or
add a separate nested-parallel model.

Vector mode has a different boundary: its formal semantics preserves sequential
order, and “innermost” is a backend acceptance condition. Do not present it as
a proof of arbitrary SIMD execution semantics without a backend bridge.

#### C2. Preserve the tiling structural/legality boundary

`TilingBoolChecker.check_pprog_tiling_sourceb` checks the exact tiled
representation, witness dimensions, positive tile sizes, source identity
witness, domain/access layout, and point-depth agreement. It never inspects
`pi_schedule`.

This is intentional. `TilingBandScheduleValidator` and its ordinary,
second-level, phase, scalar, and mixed routes add schedule-layout and
permutable/reordering facts. `PolOptBandTiling` sees a sealed direct-runtime
correctness theorem. The current direct runtime has no general affine fallback.

Required invariant for every refactor:

```text
structural source checker
  -> TilingRelation representation facts
  -> layout/band checker
  -> permutability or reordering theorem
  -> semantic equivalence
```

Never promote `check_pprog_tiling_sourceb_sound` alone as tiling correctness.
Conversely, do not merge band legality into `TilingBoolChecker`; that would
destroy a useful reusable boundary.

#### C3. Decide the parallel current-view guard contract

`ParallelValidator` checks a current-view guard, but the main soundness theorem
discards that fact. This may be an intentional conservative admission check,
because the driver supplies `current_view_pprog`, and `JamValidator` reuses the
guard. Choose and document one design before simplifying it:

- expose and consume the current-view invariant at the codegen/driver boundary;
  or
- state that the checker is intentionally stricter than `parallel_safe_dim`.

Do not silently remove the guard during proof cleanup.

### P0 proof hygiene

These changes preserve all statements and algorithms and should precede broad
abstraction work:

1. `PolyLang.v:6753`: eliminate the two `Instr.State.dummy_state` proof evars
   by supplying actual state arguments to the preceding applications.
2. `PolyLang.v:4826`: the ext flatten proof unfolds `np_lt`; make the intended
   `np_lt_ext` reasoning explicit.
3. `ISSRefinement.v:72-84`: replace two goal/hypothesis-shape `repeat match`
   blocks with an explicit named checker-success inversion lemma.
4. `TilingBandScheduleValidator.v:8460`, `8497`, `19268`, and `25145`: replace
   conjunction/hypothesis-shape matches with named construction/inversion.
   The long-proof audit identifies `8460` and `19268` as the central brittle
   sites; the other two are the same pattern in shorter proofs.
5. `ParallelCodegen.v:318`: replace `lazymatch goal` after inversion with a
   named iteration premise.
6. `ParallelPolOptCorrect.v`: replace the preparation/result `lazymatch`
   macros with Local lemmas. The file already uses an explicit theorem for the
   vector route; use that style uniformly.
7. Add proof maps and phase comments at the central bridges rather than hiding
   them under broader automation. In particular preserve the visible semantic
   stages of Extractor's 941-line mutual proof, TilingRelation's reconstruction
   and reorder bridges, and the layout-specific band reversal proofs.

No audit found evidence that generic `eauto` search is the main build-time
problem. Structural duplication and elaboration volume are stronger candidates.

## 3. Canonical owner and compatibility-wrapper matrix

The table gives the final owner, not merely the easiest existing copy. “Wrapper”
means a declaration with the current name and exact current type whose body
calls or unfolds the canonical implementation.

### 3.1 Equality and Boolean reflection

| Repeated family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| Generated `list_beq` | existing `src/Base.v:15` | Remove only the duplicate `Scheme Equality for list` command in `PolyBase.v`; no separate theorem wrapper is needed. |
| `list_Z_eqb`, affine expression, tile-link/list, statement-witness, and point-space-witness equality plus six soundness lemmas | existing `src/PointWitness.v` | Keep all same-named `AffineValidator` definitions/lemmas as exact forwarding aliases. |
| `ctxt_eqb`, `ctxt_ty_eqb`, equality specs, and reflexivity | new dependency-low `polygen/InstrContextEq.v`, functorized by `INSTR` | Keep current members in `AffineValidator`, `ISSBoolChecker`, and `TilingBoolChecker`. Do not change implication-only public theorem types; add shared iff specs under new names. |
| `forallb_imp_true_forall` and impure list traversal | impure monad/list utility beside `Vpl.Impure` | Keep `AffineValidator.forallb_imp*` paths as wrappers; retain unused head/tail names until API decision. |

### 3.2 Generic list, map, prefix, and relation facts

| Repeated family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| `nth_repeat_default` | existing `Misc.nth_repeat` | Keep `PolyBase.nth_repeat_default`. |
| Map lookup inversion/forward: `nth_error_map_inv`, `nth_error_map`, `nth_error_map_some`, `nth_error_map_fwd` | existing `Misc.nth_error_map_iff`, with named directional corollaries added there | Keep wrappers in `Extractor`, `ParallelValidator`, `TilingValidator`, `ISSRefinement`, and `TilingRelation`. |
| Combine lookup: `nth_error_combine_local`, `in_combine_nth_error_local` | existing `Misc.nth_error_combine` plus a named membership corollary | Keep `ISSSemantics` wrappers used by `ISSCutSemantics`. |
| Exact-index `Forall2_nth_error` | new exact-index corollary in `Misc.v` beside its existing existential variant | Keep `TilingRelation.Forall2_nth_error` and `ISSCutSemantics.Forall2_nth_error_local`. |
| `NoDup_map_on` | `ListExt.v` | Keep `TilingRelation.NoDup_map_on` and `ISSCutSemantics.NoDup_map_on_local`. |
| `NoDup_nth_error_injective` | `ListExt.v` | Keep `ISSRefinement.NoDup_nth_error_injective` and `TilingBandMixedSecondValidator.NoDup_nth_error_injective_local`. |
| `NoDup_map_value_unique`, filtered-index uniqueness, `NoDup`/`NoDupA` bridges | `ListExt.v` | Keep ISSCut names as wrappers. |
| `lex_compare_eq_same_length_implies_eq_local*` | a list-order fact module below PolyLang, preferably `ListExt.v` if it needs only list lexicographic comparison | Keep ISSCut and TilingBand local/public names. |
| `firstn_eq_implies_nth_eq`, `firstn_ge_implies_firstn` | `Misc.v`/`ListExt.v`; use `firstn_firstn` for the latter | Keep `PolyBase` names. |
| Extractor prefix/filter/permutation facts (`firstn_length_decompose`, `skipn_length_S_singleton`, `filter_*`, `nth_after_prefix_singleton`, `permutation_*`, `nodup_all_eq_singleton`) | `ListExt.v` | Keep every current `Extractor` name as a wrapper. |
| zip/map2 append, length, membership, `nth_error`, projections | `ListExt.v` | Keep AffineValidator paired-point helper names. |
| `seq_shift_succ`, `map_nth_seq_firstn` | `ListExt.v` | Keep ParallelValidator names. |
| `exact_listzzs_cols` head/tail/cons/app facts | `Linalg.v`, beside `exact_listzzs_cols` | Keep existing/local paths in `PrepareCodegen`, `StrengthenDomain`, `TilingBandScheduleValidator`, and any PolyBase helper names. |

`Misc.v` should remain below `ListExt.v`; do not make Misc import ListExt. Put
new facts in Misc only when they use the same low-level dependencies as its
existing map/combine/nth lemmas.

### 3.3 Linear algebra and polyhedron facts

| Repeated family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| `dot_product_repeat_zero_left` | existing `Linalg.dot_product_repeat_zero_left` | Keep `Extractor.dot_product_repeat_zero_left`. |
| Zero vector, vector negation, `opp_app`, involution, zero-negation, left/right negated dot product | new clearly named implementations in `LinalgExt.v` | Keep `PolyBase.V0`, `Vopp`, `opp_*`, `dot_product_opp_l/r`; keep `Extractor.dot_product_opp_right` and `ISSRefinement.dot_product_opp_right_local`. Avoid introducing an imported short name that collides with the wrappers. |
| One-hot/select-coordinate dot product (`v0_n_app_1...`, `dot_product_v0_app_1_nth`, `dot_product_select_coord`) | one parameterized theorem in `LinalgExt.v` | Keep `PolyBase` and `ParallelValidator` paths; TilingBand currently calls the ParallelValidator wrapper. |
| Off-index assignment lookup (`nth_assign_different`) | `Linalg.v` beside `assign` and `dot_product_assign_*` | Keep `PolyBase.nth_assign_different`. Prefer one pointwise `nth_assign` spec plus the off-index corollary. |
| `in_poly` over `map`, prefix/app inversion, `satisfies_constraint_prefix` | `Linalg.v`, beside `in_poly` | Keep PolyBase product-embedding and Extractor prefix helper names. |
| `tiling_dot_product_eq_linalg_dot_product` | new small `TilingWitnessLinalg.v` bridge | Keep `TilingRelation` theorem path if externally visible. Do not put the bridge into either core dot-product definition. |

### 3.4 Instruction points, flattening, sorting, and semantics

| Repeated family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| `instr_point_list_semantics_{nil,singleton,app}_inv` | `polygen/InstanceListSema.v` | Keep copies/paths in `Extractor`, `ParallelLoop`, and `LoopJamNative`. |
| `instr_point_sema_eq_except_sched_iff`, `eq_except_sched_symm`, `permutable_eq_except_sched` | `polygen/InstanceListSema.v`, which owns `eq_except_sched`, point semantics, and `Permutable` | Keep `ParallelValidator` names and TilingBand `_local` names as one-line wrappers. |
| `old_new_of_ext_eq_except_sched` | `PolyLang.v` beside `old_of_ext`/`new_of_ext` | Keep ParallelValidator wrapper. |
| `flatten_instrs_in_intro`, flatten member inversion, environment/current-coordinate shape, `rebase_ip_nth`, program accessors | `PolyLang.v` or a narrow `PolyLangFlattenFacts.v` importing it | Keep `Extractor`, `ISSSemantics`, and `ParallelValidator` wrappers/aliases. Moving `flatten_instrs_in_intro` removes ISSSemantics' otherwise unnecessary Extractor functor dependency. |
| Normal `InstrPoint` comparator/order block and mapped-semantics/timestamp preservation | new `PolyLangPointFacts.v` below TilingRelation and ISSCutSemantics | Keep all 17 copied `TilingRelation` and `ISSCutSemantics` names. As an immediate low-risk step, ISSCut may wrap the existing TilingRelation copy; the final owner should not remain tiling-specific. |
| “same source membership + same statement/index implies equal point” | `PolyLangPointFacts.v` | Keep the current ISSCut theorem and use it to simplify TilingRelation injectivity. |
| Generic selection sort, stable permutation, prefix movement, sorted-list uniqueness | existing `SelectionSort.v` and `StablePermut.v`, with missing parameterized theorems added | Keep `PolyLang` public theorem names as wrappers; PolyLang should retain only semantic adjacent-swap consequences. |
| `rel_list` member transport | `Base.v`, beside `rel_list_nth` and `rel_list_implies_rel_nth` | Keep ParallelValidator wrapper. |
| Iteration semantics app/refinement/state-equivalence facts | `IterSemantics.v` or a small common IterSem facts module | Keep Extractor and ParallelCodegen names. Do not import Extractor from lower modules. |

### 3.5 ISS-specific ownership

| Repeated/misplaced family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| payload equality projections/symmetry/transport and parent-child indexed lookup | new `ISSRefinementFacts.v` importing only `ISSRefinement.v` | Keep the nine current `ISSSemantics` names. Dependency order becomes `ISSRefinement -> ISSRefinementFacts -> ISSSemantics -> ISSCutSemantics`. |
| unique child occurrence under a complete cut | `ISSRefinementFacts.v` | Use it in ISSCut's 243-line injectivity proof; retain `before_of_after_point_injective_complete_cut_shape`. |
| after-to-before flattened-list iff specification | `ISSSemantics.v` | Add `before_ipl_from_after_spec`; retain `before_ipl_from_after_forward/backward` as projections. |
| ISSCut comparator/sorted-map infrastructure | final owner `PolyLangPointFacts.v` | Keep ISSCut names; do not retain TilingRelation as the permanent conceptual owner. |

### 3.6 Tiling-band-specific ownership

| Repeated/misplaced family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| Seven schedule-head/constant lemmas duplicated in Mixed and PhaseScalar | new `TilingPhaseScheduleFacts.v`, below both functors | Keep `schedule_head_constant`, `pinstr_head_constant`, `forallb_zeqb_zero_dot_product`, `schedule_head_constant_sound`, `forallb_skipn_true`, `schedule_head_constant_lift`, and `_sound` under both old paths. |
| Ordinary pair-local reversal bridge | existing Core theorem in `TilingBandScheduleValidator` | Replace Mixed's dead 502-line ordinary bridge with a wrapper/adaptor; retain its name/type. |
| Second-level pair-local reversal bridge | new Core theorem in `TilingBandScheduleValidator`, parameterized by pair-local band/recipe compatibility | Refactor Core's uniform theorem and Mixed's 586-line theorem to wrappers/adaptors. Core supplies uniform compatibility; Mixed supplies same-statement compatibility. |
| endpoint facts, composed-point facts, paired semantic/phase row packages | Local records/lemmas in `TilingBandScheduleValidator` | Keep all seven exported layout-specific reversal theorem names. Do not move layout-specific order arguments into the package. |
| ordinary/integer access-conflict traversal | one parameterized Local kernel in `AffineValidator` | Keep ordinary and integer public soundness theorem names; direct band continues to call the integer wrapper. |
| successful block-fit, projection transport, row/evaluation packages, checker-success inversion | private Core helpers in `TilingBandScheduleValidator` | Keep each current ordinary/second-level/scalar/phase specialization as a wrapper. |

### 3.7 Driver and code-generation composition

| Repeated family | Canonical owner | Compatibility wrappers/aliases |
|---|---|---|
| extractor + strengthen + route correctness + unstrengthen + extractor correctness + `State.eq_trans` | new driver-level `VerifiedRouteCorrect.v` (name tentative), parameterized by `POLIRS` and the prepared route theorem | Keep `finish_strengthened_source_correct` in `PolOptCorrect` and `PolOptBandTiling` as wrappers; replace prepared public proofs with thin applications. |
| ParallelCodegen normal/raw and parallel/vector/many erasure/refinement/correctness/fallback families | Local generic combinators in `ParallelCodegen.v` first | Keep all existing exported definitions/theorems. Move only target-AST Boolean reflection to ParallelLoop later. |
| `all_es_safeb_*`, `vector_codegen_safeb_*` | `ParallelLoop.v`, beside `trace_safe` and vector-mode placement | Keep ParallelCodegen forwarding aliases. |
| ParallelPolOpt preparation/result/alarm wrappers | Local polymorphic theorems in `ParallelPolOptCorrect.v` | Keep all 90 public route theorem names. Consider the shared driver utility only after local conversion. |
| rejection impossibility and accepted-route semantic cores | Local helpers in `PolOptBandTiling.v` | Keep route definitions and bridge-visible bodies; rebuild `SBandTilingOptBridge.v` after each factoring step. |

## 4. Recommended three-stage refactoring DAG

### Stage 0: correctness and proof stability

```text
C1 parallel semantics contract
  -> choose strong endpoint or claim limitation
  -> design interleave_family/certificate bridge

C2 tiling structure-vs-legality invariant
  -> add proof maps/integration assertions
  -> preserve direct no-fallback route

C3 current-view guard decision

independent hygiene:
  PolyLang dummy-state/ext-order fixes
  + ISSRefinement explicit inversion
  + TilingBand explicit conjunction construction
  + ParallelCodegen named inversion premise
  + ParallelPolOpt theorem-based orchestration
```

No file split or dead API removal belongs in Stage 0. Establish a clean full
`coqc` baseline, existing tests, and per-file timings before and after. Do not
add or use `coqchk`; the accepted proof gate is the normal clean `coqc` build
plus existing CI/tests.

### Stage 1: API-preserving canonicalization and Local factoring

Dependency order:

```text
Misc/ListExt
  -> Linalg/LinalgExt
  -> InstanceListSema/IterSemantics
  -> PolyLangPointFacts + PolyLang wrappers
  -> PolyBase / Extractor / ParallelValidator / AffineValidator wrappers

PointWitness + InstrContextEq
  -> AffineValidator / ISSBoolChecker / TilingBoolChecker wrappers

ISSRefinement
  -> ISSRefinementFacts
  -> ISSSemantics specification
  -> ISSCut injectivity/reconstruction

TilingBandScheduleValidator Local packages
  -> Core ordinary pair bridge
  -> new Core second-level pair bridge
  -> Mixed adaptors
  -> PhaseScalar and DirectRuntime consumers

local driver lifting theorem
  -> PolOptCorrect wrappers
  -> PolOptBandTiling wrappers
  -> shared driver utility prototype
  -> ParallelPolOptCorrect migration
```

Within large files, use these local orders:

- **Extractor:** low-level wrappers -> headings -> private constructor case
  lemmas around `core_sched_stmt_stmts_constrs_prefix_mutual` -> legacy wrapper
  decisions.
- **PolyLang:** proof hygiene -> live retiming route -> generic sort wrappers ->
  private normal/ext flatten skeleton -> semantic swap equivalence.
- **AffineValidator:** PointWitness aliases -> ordinary/integer access kernel ->
  paired flatten helpers -> semantic symmetry -> top-level wrapper unification.
- **TilingRelation:** collapse duplicated `...exists_perm_source` -> index/env
  Local facts -> canonical one-point decomposition -> source theorem rewrites ->
  generic wrapper moves.
- **TilingBand Core:** exact ParallelCore wrappers -> explicit goal construction
  -> block-fit helper -> endpoint packages -> guarded-pair kernel -> projection
  and evaluation packages.
- **ParallelValidator:** canonical wrappers -> single-point synthetic-view fact
  -> two-point reversal fact -> orientation-independent transport -> rewrite the
  333-line theorem.

Every canonicalization step must compile the owner, compatibility wrappers, and
direct consumers before moving to the next layer.

### Stage 2: physical boundaries and API decisions

Only after Stage 1 stabilizes:

1. Split `TilingRelation` into representation, erasure, reconstruction, and
   semantics modules, leaving `TilingRelation.v` as a compatibility re-export.
   Narrow imports for representation-only validators; otherwise the split gives
   little incremental-build benefit.
2. Prototype direct functor imports: PhaseScalar should instantiate Schedule
   Core directly; DirectRuntime should instantiate PhaseScalar and Mixed
   independently. Keeping `PhaseScalar.Mixed` preserves API but also preserves
   the expensive nested instantiation, so this requires an explicit path/API
   decision and timing comparison.
3. Split Extractor only after generic facts and obsolete routes are removed or
   wrapped. The natural boundary is frontend checks/executable extraction versus
   loop-semantic reconstruction; preserve the `Extractor` functor facade.
4. Split PolyLang codec/flatten proofs only after lower generic order/sort facts
   move out. Preserve projections, constructors, notations, and module aliases.
5. Decide exported dead/legacy policy module by module. Prefer deprecation
   wrappers over keeping duplicate proof bodies. Remove paths only in a declared
   breaking cleanup.

### Two-stage fallback

If the project wants a smaller operational plan, merge Stages 0 and 1 into an
“API-preserving stabilization” branch, then perform Stage 2 in a separate
“module/API cleanup” branch. Do not merge the parallel semantic-gap work with
dead-code deletion; it needs independent review and claims validation.

## 5. P1 Local factoring targets

The highest-payoff nonsemantic reductions are:

1. **TilingBand:** seven reversal bridges share 6,370 proof lines of endpoint
   and schedule reconstruction. Package facts, but retain layout-specific order
   reasoning.
2. **Mixed second-level:** move the repeated 586-line Core algorithm behind the
   new pair-local Core bridge; replace the dead 502-line ordinary proof with an
   existing Core adaptor.
3. **Extractor:** split the 941-line mutual proof into private instruction,
   loop, sequence, and guard case lemmas; keep the mutual theorem as the visible
   induction center.
4. **ParallelValidator:** split the 333-line theorem into single-point data,
   same-slice reversal, and final transport.
5. **AffineValidator:** parameterize the ordinary/integer access-conflict kernel;
   the 305-line integer theorem should become a wrapper.
6. **TilingRelation:** one canonical retiled-point decomposition should feed
   belongs-to, injectivity, timestamp, instruction semantics, and preimage
   theorems; the `exists_perm_source` theorem should call the immediately
   preceding existence theorem plus sort permutation.
7. **ISSCut:** obtain unique child occurrence from ISS refinement facts and use
   it to rewrite the 243-line injectivity proof.
8. **PolyLang:** private normal/ext flatten skeleton and a symmetric semantic
   list-equivalence relation remove mirror proofs without merging public records.
9. **Driver files:** theorem-level route lifting replaces repeated extraction,
   strengthening, result inversion, and equality composition.

Avoid high-order generic scanners or tactics when only two short proofs share a
shape. Examples that should mostly keep explicit structure are
`TilingBoolChecker`'s source statement/program reflection proofs and
layout-specific strip-mining/phase-order arguments.

## 6. P2 dead and compatibility routes

High-volume candidates, all requiring an API decision:

- **Extractor:** 101 declarations outside the confirmed-public closure; 43
  exact zero-reference declarations. The alternate predecessor/non-prefix and
  old fuel routes dominate the unused proof volume.
- **PolyLang:** 75 declarations outside the confirmed-public closure; the
  16-declaration `same_np_set` route costs about 499 proof lines.
- **AffineValidator:** 44 unreachable declarations, including old non-`_at`
  pairing/flatten clusters and the rational guard route.
- **TilingRelation:** 62 exported declarations outside the current public
  closure; clean the active source route before the compiled/general route.
- **TilingBoolChecker:** the six-member compiled Boolean checker chain is
  repository-inactive. Its declarative compiled relation in TilingRelation is
  not dead.
- **TilingBandScheduleValidator:** 28 long proofs are outside both runtime and
  confirmed external-root closure; isolate the old `via_validate_tiling` route
  but preserve names initially.
- **Mixed:** three-member unique-phase ordinary route is superseded by the
  phase-class/Core bridge.
- **ISSSemantics:** seven-member before-to-after search branch is unfinished and
  unused; the after-to-before representation route is active.
- **ISSRefinement:** five repository-unreferenced utilities, none long.
- **ISSCut:** one unused payload projection.
- **ParallelValidator:** nine unreachable names, including obsolete standalone
  well-formedness and direct old/new-domain routes.
- **ParallelCodegen:** nine unreachable names; the origin-depth chain may be a
  seed for the missing correctness bridge and must not be deleted before C1.
- **ParallelLoop:** unused `interleave_family` and
  `family_ordered_permutable` are likely required for C1; other conversion and
  base-loop clusters can be reviewed later.
- **PolOptCorrect:** current configuration does not call several natural public
  wrappers; retain top-level theorem names and dormant ISS support.

## 7. Completed coverage

| File | Declarations | Long proofs reviewed/indexed | Main artifact |
|---|---:|---:|---|
| `src/Extractor.v` | 263 | 60 | `/tmp/polcert-extractor-audit-summary.md` |
| `src/PolyLang.v` | 401 | 37 | `/tmp/polcert-polylang-audit-summary.md` |
| `src/PolyBase.v` | 108 | 15 | `/tmp/polybase_summary.md` |
| `src/AffineValidator.v` | 176 | 23 | `/tmp/polcert-affinevalidator-audit-summary.md` |
| `src/TilingRelation.v` | 221 | 47 | `/tmp/tiling_relation_audit.md` |
| `src/TilingBoolChecker.v` | 25 | 2 | `/tmp/tiling_bool_checker_summary.md` |
| `src/TilingBandScheduleValidator.v` | 818 | 114 | `/tmp/tiling-band-proof-audit.md` |
| `src/TilingBandMixedSecondValidator.v` | 51 | 8 | `/tmp/tiling_band_mixed_second_summary.md` |
| `src/TilingBandPhaseScalarValidator.v` | 51 | 7 | `TILING_BAND_PHASE_SCALAR_VALIDATOR_AUDIT.md` |
| `src/TilingBandDirectRuntime.v` | 18 | 5 | `TILING_BAND_DIRECT_RUNTIME_AUDIT.md` |
| `src/TilingValidator.v` | 74 | 5 | `TILING_VALIDATOR_AUDIT.md` |
| Canonical tiling and ISS facade/witness group | 144 | 4 | `VALIDATOR_FACADES_AUDIT.md` |
| `src/ISSRefinement.v` | 69 | 3 | `/tmp/iss-refinement-summary.md` |
| `src/ISSSemantics.v` | 28 | 3 | `/tmp/iss_semantics_summary.md` |
| `src/ISSCutSemantics.v` | 36 | 6 | `/tmp/polcert-isscutsemantics-audit-summary.md` |
| `src/ParallelValidator.v` | 68 | 2 | `/tmp/polcert-parallelvalidator-audit-summary.md` |
| `src/ParallelCodegen.v` | 90 | 1 | `/tmp/parallel-codegen-summary.md` |
| `src/PrepareCodegen.v` | 79 | 14 | `PREPARE_CODEGEN_AUDIT.md` |
| `polygen/CodeGen.v` | 13 | 1 | `CODEGEN_AUDIT.md` |
| Shared owner libraries (`Misc`, `ListExt`, `Linalg*`, `InstanceListSema`) | 401 | 9 | `CANONICAL_OWNER_LIBRARIES_AUDIT.md` |
| Frontend and final facade group | 218 | 4 | `END_TO_END_FACADES_AUDIT.md` |
| `polygen/ParallelLoop.v` | 129 | 7 | `/tmp/polcert-parallelloop-audit-summary.md` |
| `driver/ParallelPolOptCorrect.v` | 135 | 9 | `/tmp/parallel-polopt-summary.md` |
| `driver/PolOptBandTiling.v` | 64 | 9 | `/tmp/polcert-poloptbandtiling-audit-summary.md` |
| `driver/PolOptCorrect.v` | 12 | 1 | `/tmp/polcert-poloptcorrect-audit-summary.md` |

## 8. Files and long proofs not yet comprehensively audited

The following files have not received the same declaration/caller/public-root
and individual-long-proof review. `/tmp/uncovered_long_proofs.txt` is only a
lightweight current-source scan; it is not a substitute for the full audit.

### Tiling facades not yet covered

The canonical tiling and ISS facade/witness files are now covered by
`VALIDATOR_FACADES_AUDIT.md`.  Remaining tiling work here concerns lower
code-generation and cleanup modules rather than these validator facades.

### Frontend and driver facades

`driver/ParallelPolOpt.v` and `driver/SParallelPolOptBridge.v` have no current
proof spanning 30 lines, but their executable route/API declarations have not
received full reachability audits. The completed audit covers
`ParallelPolOptCorrect.v` and the five-file frontend/final facade group, not
`ParallelPolOpt.v` itself.

`PointWitness.v` has no long proof and its equality API was inspected only as a
duplication owner, not audited declaration by declaration.

### Broader first-party modules outside the completed audit set

The proposed canonical owners `Misc.v`, `ListExt.v`, `Linalg.v`,
`LinalgExt.v`, and `InstanceListSema.v` are now audited.  Large or semantically
relevant modules still outside the same standard include `CState.v`,
`CInstr.v`, `Convert.v`, `LoopUnroll.v`, `LoopCleanup.v`, `LoopJamNative.v`,
`SelectionSort.v`, and `StablePermut.v`.

## 9. Acceptance and measurement gates

For every Stage 1 batch:

1. preserve a normalized public API inventory before/after;
2. compile the canonical owner first, then wrapper modules, then direct
   consumers;
3. run a clean full `coqc` build and existing CI/tests;
4. record isolated wall time and peak RSS for the edited large files;
5. record incremental rebuild after touching only a late proof module;
6. compare `.vo` sizes and `coqdep` predecessor counts for physical-boundary
   prototypes;
7. do not treat shorter source or more parallel jobs as proof of improvement
   without timings.

The highest-value first implementation batch is:

```text
P0 proof-hygiene fixes
  + PointWitness exact wrappers
  + Misc map/combine wrappers
  + InstanceListSema eq_except_sched transport
  + TilingBand Core pair-local second-level bridge
```

The parallel semantic-gap theorem should proceed on a separate branch with its
own review because it changes the strength of the verified endpoint rather than
only its readability.
