# ParallelPolOptCorrect read-only audit summary

- 2,612 source lines; 135 declarations: 129 proofs and 6 Ltac declarations.
- 9 proofs have inclusive `Proof`..`Qed` spans of at least 30 lines.
- `VerifiedParallelCompilerConfig.v` directly uses 30 final `Opt_*_correct`
  theorems. All 135 declarations are transitively reachable from those roots.
- 131 declarations are public; the only Local declarations are four proof
  macros. Preserve every current public name and type.

## Main finding

This file contains orchestration, not new transformation theory. Its long
proofs invert executable route control flow and compose correctness theorems
owned by extraction, strengthening, ISS, affine validation, tiling,
annotation, and code generation.

The largest readability issue is asymmetric proof reuse across 90 route
instances:

- 30 prepared-route theorems; 27 use three `lazymatch goal` macros.
- 30 result-route theorems; 20 parallel variants use a 46-line Ltac, while 10
  vector variants use an explicit generic lemma for the same composition.
- 30 alarm-free entry theorems; 20 parallel variants copy a 9-line proof,
  while 10 vector variants use an explicit generic lemma.

## Recommended order

1. Replace the extraction Ltac with one polymorphic Local Lemma; retain the
   existing public vector helper as a specialization wrapper.
2. Add one polymorphic Local result-unwrapping lemma for all 30 final routes.
3. Replace the three prepared-route goal-matching macros with an explicit
   preparation + annotation composition lemma and affine/ISS adapters.
4. Give verified tiling and diamond routes named success views so semantic and
   wf theorems do not destruct the same failure tree independently.
5. Parameterize no-ISS/with-ISS runner duplicates and ordinary/diamond
   optional-ISS fallback proofs.

These changes should preserve route definitions, fallback behavior, and every
public theorem type. New helpers should remain Local until a later cross-driver
utility refactor is justified.

---

# Read-only audit: driver/ParallelPolOptCorrect.v

## Scope and parser

- Source lines: 2,612. Parsed declarations: 135, consisting of 129 proof-bearing Lemma/Theorem declarations and 6 Ltac declarations.
- One root functor module is present. Module aliases are not treated as nested scopes; there are no Sections, mutual `with` declarations, admitted proofs, or nested declaration modules.
- Proof length is the inclusive `Proof` through `Qed` span; 9 proofs are at least 30 lines. Ltac bodies are audited separately because four macros span 35-46 declaration lines but have no `Proof` block.
- Caller and reachability edges are conservative token references across complete declarations; local shadowing can over-approximate an edge. Qualified external matching anchors the final component to a known declaration, so theorem-ending periods are not mistaken for module separators.

## Public reachability

- `driver/VerifiedParallelCompilerConfig.v` directly uses 30 final `Opt_*_correct` theorems. These are exactly the qualified external roots of this file.
- All 135 declarations, including the 4 Local Ltac macros, are transitively reachable from those 30 config roots. There is no dead or legacy-only theorem family in this file.
- 131 declarations are public. Intermediate preprocessing/prepared/result lemmas have no direct qualified external user, but are on a public correctness path; preserve every existing public name and type. New composition helpers should be `Local Lemma`s.

## Responsibility boundary

- This driver should own **control-flow inversion and semantic composition** across extraction, strengthening, optional ISS, affine validation, tiling validation, annotation, and codegen.
- It should not reproach ISS, affine scheduling, tiling, parallelization, vectorization, or code-generation semantics. The current long proofs correctly delegate those facts to their owning modules; none contains new transformation theory.
- Generic impure/result combinators belong in `Result` only if they are independent of LoopIR/PolyLang. The extraction/strengthening and preparation/annotation lemmas are domain-specific and should initially remain Local in this driver or a small driver-private correctness utility.

## Structural duplication

- **90 route-instance theorems:** 30 prepared-route theorems, 30 extraction/result theorems, and 30 alarm-free entry theorems. Their route names are useful public API; their proof implementation should be shared.
- **Prepared routes:** 27 of 30 are discharged by three goal-matching Ltac macros; 3 identity routes call codegen correctness directly.
- **Result routes:** 20 parallel theorems use `finish_extracted_result`; 10 vector theorems use the explicit `opt_vector_current_result_from_prepared_correct` lemma. This is the same composition expressed two ways.
- **Alarm-free routes:** 20 parallel proofs copy the same 9-line result-unwrapping script; 10 vector proofs reuse `opt_vector_current_from_result_correct`. A single polymorphic helper can serve all 30.
- **Semantic/wf pairs:** every preprocessing route proves backward semantics and wf by separately destructing the same executable control flow. A private success-view or combined route spec should be proved once and projected into the unchanged public theorem pair.

## P0/P1 order

1. **P0.1:** replace `finish_extracted_result` with a polymorphic Local extraction/strengthening lemma; make `opt_vector_current_result_from_prepared_correct` a public specialization wrapper; route all 30 result theorems through it.
2. **P0.2:** introduce a polymorphic Local result-unwrapping lemma; retain `opt_vector_current_from_result_correct` as a wrapper and use the helper in all 20 parallel plus 10 vector entry proofs.
3. **P0.3:** replace the three prepared-route lazymatch macros with a Local preparation + annotation semantic-composition lemma and small affine/ISS adapters.
4. **P0.4:** introduce success-view records/lemmas for verified tiling and diamond. Prove correctness and wf projections without repeating failure trees.
5. **P1.1:** parameterize the duplicated no-ISS/with-ISS phase-runner proofs and the ordinary/diamond optional-ISS fallback proofs.
6. **P1.2:** selectively replace `eauto` after helper signatures stabilize. Do not churn already transparent one-line wrappers.
7. **P1.3:** consider a cross-driver extraction/strengthening correctness utility only after the local refactor is stable; equivalent code also exists in `PolOptCorrect.v`, `PolOptCanonicalTiling.v`, and other drivers.

## Tactic audit

- Four Local macros use `lazymatch goal`; there is no ordinary `match goal`, `repeat`, `try`, `intuition`, or `firstorder` in this file. The problem is not uncontrolled search but hidden goal-shape coupling.
- There are 100 `eauto` calls across 72 declarations, 15 standalone `auto` calls across 11 declarations, and 57 `bind_imp_destruct` sites. No custom-depth or database-qualified `eauto` is present.
- `reject_tiling_contradiction` is invoked 60 times across 22 declarations. This repetition reflects explicit fail-closed route branches; a success-view lemma can eliminate most calls while making accepted evidence clearer.

## All >=30-line proofs

### `try_verified_tiling_after_phase_mid_poly_correct` (declaration 114; proof span 35, body 33)

- **Role:** Inverts witness inference, canonical target import, direct-band route acceptance, and target wf checking; then applies the runtime tiling theorem.
- **Why long:** The semantic argument is only the final validator call. Four rejected branches are proved impossible by repeating the rejection tactic.
- **Refactor:** Introduce a private success-view lemma for `try_verified_tiling_after_phase_mid_poly`; prove a combined wf + semantic-backward spec once, and leave this theorem and its 28-line wf partner as projections.
- **Risk/use:** `low`; callers 2; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_phase_pipeline_from_source_pol_poly_correct` (declaration 195; proof span 31, body 29)

- **Role:** Composes schedule-only affine validation from the source to the phase midpoint with verified tiling from midpoint to target.
- **Why long:** Three executable failure branches plus manual unpacking of the two semantic witnesses and `State.eq_trans` account for the size.
- **Refactor:** Use a private two-stage validated-route composition lemma. Keep the affine validator and tiling theorem names explicit in the instantiation.
- **Risk/use:** `low`; callers 2; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_identity_tiling_phase_pipeline_from_source_pol_poly_correct` (declaration 263; proof span 32, body 30)

- **Role:** Specializes the phase pipeline to Pluto identity tiling and the `from_openscop_like_source` midpoint importer.
- **Why long:** It copies the preceding affine-midpoint + tiling composition almost verbatim; only the runner and midpoint importer differ.
- **Refactor:** Parameterize a private phase-pipeline proof over runner/importer evidence, or at minimum share the semantic composition tail. Keep this public specialization unchanged.
- **Risk/use:** `medium`; callers 1; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_verified_diamond_after_phase_mid_poly_correct` (declaration 333; proof span 56, body 54)

- **Role:** Proves the three-stage diamond route: verified tiling to `pol_posttile`, general affine validation to `pol_after`, then semantic composition back to `pol_mid`.
- **Why long:** The largest proof is executable control-flow inversion: witness/import/route/wf/post-affine/wf produce deeply nested branches. The only semantic step is composing post-affine and tiling results.
- **Refactor:** P0: define a named success-view record for the diamond route containing `pol_posttile`, `pol_after`, both wf facts, direct-band acceptance, and post-affine validation; prove semantic composition from that record.
- **Risk/use:** `medium`; callers 2; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_verified_diamond_after_phase_mid_poly_wf` (declaration 400; proof span 38, body 36)

- **Role:** Shows successful diamond output is generally well formed.
- **Why long:** It repeats the exact nested control-flow tree from the correctness theorem solely to recover the last target wf check.
- **Refactor:** Derive this as a projection of the same diamond success-view/combined spec used by the correctness theorem.
- **Risk/use:** `low`; callers 2; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_post_tiling_affine_phase_pipeline_from_source_pol_poly_correct` (declaration 447; proof span 32, body 30)

- **Role:** Runs the no-ISS diamond phase producer, validates the affine midpoint, and invokes verified diamond correctness.
- **Why long:** It duplicates the generic phase composition pattern and the with-ISS diamond theorem; only the phase runner differs.
- **Refactor:** Introduce a runner-parameterized private diamond-phase composition lemma and keep no-ISS/with-ISS names as wrappers.
- **Risk/use:** `low`; callers 2; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_post_tiling_affine_phase_pipeline_from_source_pol_poly_with_iss_correct` (declaration 556; proof span 32, body 30)

- **Role:** Runs the ISS-enabled diamond phase producer, validates the affine midpoint, and invokes the same verified diamond theorem.
- **Why long:** The proof is structurally identical to the no-ISS variant apart from the runner constant.
- **Refactor:** Use the same runner-parameterized private lemma as the no-ISS theorem; preserve this public name/type.
- **Risk/use:** `low`; callers 1; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_checked_iss_post_tiling_affine_phase_pipeline_from_poly_poly_correct` (declaration 626; proof span 32, body 30)

- **Role:** Implements optional ISS: if inference, ISS validation, and wf checking succeed, compose ISS semantics with the with-ISS diamond route; otherwise prove the fallback diamond route.
- **Why long:** Four fallback branches repeat the same downstream theorem; the accepted branch manually composes ISS and route state equivalences.
- **Refactor:** Factor a private optional_checked_iss_route_correct combinator parameterized by accepted and fallback route theorems. Pair it with the 19-line wf theorem.
- **Risk/use:** `medium`; callers 1; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

### `try_checked_iss_phase_pipeline_from_poly_poly_correct` (declaration 814; proof span 35, body 33)

- **Role:** Implements the same optional-ISS/fallback policy for the ordinary phase pipeline.
- **Why long:** It duplicates the checked-ISS diamond control-flow proof with different accepted/fallback route theorems.
- **Refactor:** Instantiate the same optional_checked_iss_route_correct combinator; keep the ordinary and diamond policies explicit at call sites.
- **Risk/use:** `medium`; callers 1; direct qualified external uses 0; config-reachable `yes`. Public name/type must remain unchanged.

## Ltac declarations

### `reject_tiling_contradiction` (Public, line 62, declaration span 3)

- **Diagnosis:** A three-line convenience wrapper around a public no-return lemma. It hides no semantic reasoning, though it is currently exported because it lacks `Local`.
- **Refactor:** Retain for API stability; new code can call the no-return lemma directly or a Local wrapper.
- **Use:** callers 22; config-reachable `yes`.

### `reject_post_tiling_affine_contradiction` (Public, line 65, declaration span 3)

- **Diagnosis:** Same narrow role for rejection after the post-tiling affine phase.
- **Refactor:** Retain for API stability; no priority refactor.
- **Use:** callers 2; config-reachable `yes`.

### `finish_checked_annotation_after_preparation` (Local, line 1079, declaration span 35)

- **Diagnosis:** At 18 call sites it destructs preparation, proves output wf, applies annotation/codegen correctness, applies preparation correctness, and composes `State.eq`. The lazymatch requires hypotheses with exact names/types/shapes.
- **Refactor:** Replace with a Local semantic-composition lemma parameterized by preparation wf/correctness and annotation correctness.
- **Use:** callers 18; config-reachable `yes`.

### `finish_checked_affine_annotation` (Local, line 1114, declaration span 37)

- **Diagnosis:** At 3 call sites it inlines affine scheduler wf/correctness before the same annotation composition.
- **Refactor:** Make it a specialization of the same Local prepared-annotation lemma using scheduler correctness adapters.
- **Use:** callers 3; config-reachable `yes`.

### `finish_checked_iss_annotation` (Local, line 1151, declaration span 40)

- **Diagnosis:** At 6 call sites it repeats the general macro but asks for affine wf of the prepared program.
- **Refactor:** Use the same Local lemma after converting affine wf to general wf; avoid a separate goal-matching macro.
- **Use:** callers 6; config-reachable `yes`.

### `finish_extracted_result` (Local, line 1518, declaration span 46)

- **Diagnosis:** At 20 parallel result theorems it performs extraction, strengthening, prepared-route correctness, unstrengthening, extractor correctness, and equality composition. The later explicit `opt_vector_current_result_from_prepared_correct` proves the same pipeline.
- **Refactor:** Replace both with one polymorphic Local lemma over the route argument type; retain the public vector helper as a specialization wrapper.
- **Use:** callers 20; config-reachable `yes`.

## Interface rule

- Preserve every existing public Lemma/Theorem/Ltac name and type. Route-specific theorem names are useful documentation even when their proofs become one-line specializations.
- Replace Local Ltac implementations freely with Local Lemmas; they are not part of the exported module signature.
- Do not merge route definitions or alter fallback behavior as part of a readability cleanup. The refactor should change proof organization only.
