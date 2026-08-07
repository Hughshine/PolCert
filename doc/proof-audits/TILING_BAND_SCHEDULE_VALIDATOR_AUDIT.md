# Read-only audit: TilingBandScheduleValidator.v

## Scope and method

- Source: `src/TilingBandScheduleValidator.v` (28,714 lines in the audited checkout).
- Parsed declarations: 818; proof-bearing declarations: 503; proofs with inclusive `Proof`..terminator span >=30 lines: 114.
- The parser strips nested comments while preserving line numbers, recognizes one-line proofs, distinguishes module aliases from module scopes, and records mutual declarations. The file has one root functor, no nested module declaration scope, and no mutual `with` declaration.
- Internal caller/reachability edges are conservative token-level references over complete declarations; identifier shadowing can over-approximate an edge. Qualified external uses permit whitespace/newlines around dots. Unqualified uses after `Import` are intentionally not claimed as qualified uses.
- A confirmed external root is any declaration referenced with a qualified name from another repository `.v` file. A runtime root is a `Legacy.<name>` reference in `src/TilingBandDirectRuntime.v`. Reachability follows internal declaration dependencies from those roots.
- All declarations in this functor are non-`Local`; therefore even repository-unreferenced names remain exported API. Recommendations retain every public name and type.

## Confirmed public entry boundary

- The externally visible runtime route is defined in `src/TilingBandDirectRuntime.v` as `checked_tiling_schedule_sourceb_first_runtime_validate_route`, with `checked_tiling_schedule_sourceb_first_runtime_validate_route_correct` as its correctness theorem.
- The target-file runtime roots are the 31 declarations referenced as `Legacy.<name>` by that runtime module; they are listed in `/tmp/tiling-band-proof-index.md`. This is stricter than treating every exported declaration in the functor as a current runtime entry.
- The current runtime file contains no `via_validate_tiling` or `validate_tiling` reference. The legacy chain remains exported compatibility API, but it is not on this runtime path.

## Responsibility boundaries

|section|lines|long proofs|responsibility|
|---|---:|---:|---|
|`CommonBandInfrastructure`|52-2860|8|Schedule projection, flattening transport, and common band data.|
|`SecondLevelShapeRecognition`|2862-6679|16|Second-level recipe/layout recognition and schedule evaluation.|
|`ProjectedScheduleBridge`|6681-8971|10|Projection equivalence, strip-mined order lemmas, endpoint provenance, and old compatibility bridge.|
|`CommonBandDirectChecker`|8973-13995|24|Legacy fallback compatibility plus the current ordinary/second-level direct affine-guard route.|
|`PerStatementBandChecker`|13997-14385|1|Statement-specific componentwise band validation.|
|`SemanticBandKernel`|14387-15115|3|Layout-independent semantic-row guard and pair/component validation.|
|`ProgramWideSemanticReconstruction`|15117-21038|23|Ordinary/second-level global semantic rows and reversal bridges.|
|`ScalarAwareBands`|21040-24214|14|Mixed scalar/active-band layouts.|
|`PhaseAwareSemanticBands`|24216-28667|15|Phase-aware ordinary and second-level semantic layouts.|
|`ExecutableExamples`|28669-28712|0|Closed executable examples; no >=30-line proof.|

## Strict cleanup order

1. **P0.1 exact reuse:** replace the local ParallelCore duplicates with exact qualified wrappers.
2. **P0.2 goal-shape removal:** replace the two long-proof `match goal` constructions (and the related 27-line phase exact-cols proof) with explicit named construction; central proof search must not depend on incidental conjunction shape.
3. **P0.3 duplicated bounds:** introduce one private successful-block-fit lemma for ordinary and second-level inference.
4. **P0.4 endpoint fact package:** define private `composed_point_facts` and paired semantic/phase row packages; use them in all seven 596-1336-line reversal bridges. Keep each exported theorem and each layout-specific order argument.
5. **P0.5 guarded-pair kernel:** factor collision/access-to-permutability and traversal scaffolding across ordinary, semantic, scalar-aware, and per-statement direct checkers. Keep guard-construction theorems layout-specific.
6. **P0.6 direct composition:** simplify route-level correctness wrappers after P0.4/P0.5, without hiding the composition boundary.
7. **P1.1 utility sinking:** move generic affine/list lemmas to a low-level utility, avoiding imports from higher-level validators; retain wrappers for every current name.
8. **P1.2 projection abstraction:** replace seven projection/flattening copies with one law-driven transport theorem and public specialization wrappers.
9. **P1.3 evaluation/row packages:** share exact-column, lifted-evaluation, padded-identity, paired-row, and global-slot facts.
10. **P1.4 checker inversion:** replace repeated nested option/boolean destruction with named success-inversion lemmas, not broad automation.
11. **P1.5 local cleanup:** clean the small structural proofs that only marginally exceed 30 lines.
12. **P1.6 retain theory core:** do not aggressively genericize strip-mining, zero-erasure, scalar-prefix, or phase order arguments; these expose the formal insight.
13. **P1.7 legacy isolation:** group the runtime-unreachable `via_validate_tiling` chain as compatibility code while preserving all qualified names/types.

## Quantitative findings

- Long proofs by section: `CommonBandInfrastructure` 8, `SecondLevelShapeRecognition` 16, `ProjectedScheduleBridge` 10, `CommonBandDirectChecker` 24, `PerStatementBandChecker` 1, `SemanticBandKernel` 3, `ProgramWideSemanticReconstruction` 23, `ScalarAwareBands` 14, `PhaseAwareSemanticBands` 15.
- Refactor risk classification: low 55, medium 48, high 11. High means the recommendation is to retain the mathematical core, not that the current proof is unsound.
- Long proofs not reachable from the current runtime roots: 28; also unreachable from any confirmed qualified external root: 28. They remain exported API.
- Largest concentration: the seven local/program-wide reversal bridges contain 6,370 inclusive proof lines. Their common readability issue is endpoint/schedule reconstruction duplication, while their layout-specific order arguments are genuine theory.

## Tactic-shape audit

- Among the 114 long proofs, there are exactly two goal-shape tactic sites: `repeat match goal with |- _ /\ _ => split end` at line 8460 and a hypothesis-shape `match goal` at line 19268. A related hypothesis-shape match occurs at line 25145 in a 27-line proof. These are P0.2 because harmless changes to conjunction shape or hypothesis naming can break them.
- The long proofs contain 175 `eauto` calls across 60 proofs, 15 standalone `auto` calls across 11 proofs, and 20 `tauto` calls across 7 proofs. There is no `intuition`, `firstorder`, custom high-depth `eauto`, or database-qualified `eauto`. Most `eauto` calls immediately finish premises after a named `eapply`; they are not by themselves evidence of theoretical complexity or a compilation bottleneck. Replace them selectively after helper extraction when the exact premises become stable.

## Complete long-proof audit

### CommonBandInfrastructure

#### `permutable_eq_except_sched_local` (line 946; span 46, body 44)

- **Responsibility:** Transfers schedule-only equality into the existing permutability relation.
- **Why long:** The proof and its two local prerequisites duplicate ParallelCore lemmas.
- **Refactor:** Keep this public name/type as a one-line wrapper around ParallelCore.permutable_eq_except_sched; do the same for the two short prerequisites.
- **Order/risk:** `P0.1 exact reuse` / `low`.
- **Use:** internal callers 5; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instr_nth_ext_project_band` (line 1981; span 62, body 60)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instr_nth_ext_project_pluto_band` (line 2051; span 62, body 60)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_project_band` (line 2155; span 77, body 75)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_project_pluto_band` (line 2240; span 78, body 76)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_project_pluto_band_component` (line 2326; span 84, body 82)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_project_pluto_bands_component` (line 2437; span 141, body 139)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_project_cutoff` (line 2588; span 84, body 82)

- **Responsibility:** Transports flattened instruction instances, NoDup, and lexicographic sorting through a schedule projection.
- **Why long:** Seven specializations repeat the same forward membership, restored-point, injectivity, and Sorted-map argument; the multi-band theorem adds only nth-error alignment.
- **Refactor:** Prove one private projection-transport theorem from restore/belongs/injective/order-preserving laws, then leave every exported theorem as a specialization wrapper.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

### SecondLevelShapeRecognition

#### `second_level_band_recipe_of_links_aux_sound` (line 2939; span 38, body 36)

- **Responsibility:** Shows that the executable link parser returns a well-formed second-level band recipe.
- **Why long:** Length comes from recursive option/boolean inversion aligned with the link-list recursion.
- **Refactor:** Keep the induction visible; only factor named inversion lemmas for successful parser branches.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `eval_tile_links_from_second_level_recipe_spec` (line 3128; span 83, body 81)

- **Responsibility:** Evaluates root/child tile links described by a recognized second-level recipe.
- **Why long:** This is a genuine structural induction over the recipe/link pairs, not accidental tactic expansion.
- **Refactor:** Keep as the semantic core; extract only recurring arithmetic side conditions if they obtain stable names.
- **Order/risk:** `P1.6 retain theory core` / `medium`.
- **Use:** internal callers 3; qualified external uses 2; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `eval_tile_links_from_schedule_rows_aux` (line 3898; span 56, body 54)

- **Responsibility:** Connects witness schedule rows to quotient values produced by tile-link evaluation.
- **Why long:** A genuine induction over links repeatedly opens exact-column and nth-row evidence.
- **Refactor:** Retain the induction; reuse a small row-lookup/exact-column helper shared with later semantic-row proofs.
- **Order/risk:** `P1.3 row lookup helper` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `compose_tiling_pinstr_ext_wf_tiling_local` (line 4168; span 46, body 44)

- **Responsibility:** Shows that composing the first and second tiling witnesses preserves the local well-formed tiling relation.
- **Why long:** The body reconstructs record fields and discharges repeated length/evaluation obligations.
- **Refactor:** Introduce a private constructor lemma for composed witness facts; keep this theorem as the public wrapper.
- **Order/risk:** `P1.3 composition helper` / `medium`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `affine_product_identity_affine_row` (line 4756; span 32, body 30)

- **Responsibility:** Evaluates identity affine rows at a selected coordinate or suffix of coordinates.
- **Why long:** The proofs manually repeat nth/skipn arithmetic that is independent of tiling.
- **Refactor:** Move the general coordinate-selection fact to a low-level affine utility and preserve both names as wrappers; do not import a higher-level validator module.
- **Order/risk:** `P1.1 utility sinking` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `affine_product_identity_affine_rows_from` (line 5011; span 50, body 48)

- **Responsibility:** Evaluates identity affine rows at a selected coordinate or suffix of coordinates.
- **Why long:** The proofs manually repeat nth/skipn arithmetic that is independent of tiling.
- **Refactor:** Move the general coordinate-selection fact to a low-level affine utility and preserve both names as wrappers; do not import a higher-level validator module.
- **Order/risk:** `P1.1 utility sinking` / `low`.
- **Use:** internal callers 6; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `stripmine_schedule_after_env_eval` (line 5068; span 72, body 70)

- **Responsibility:** Computes the target timestamp produced by ordinary, grouped second-level, or interleaved strip-mining after an environment prefix.
- **Why long:** Each proof repeats lifted-schedule evaluation, exact-column bookkeeping, and prefix/band/suffix splitting; layout-specific ordering remains real content.
- **Refactor:** Factor private lifted-schedule and identity-block evaluation packages, then keep the three layout theorems explicit specializations.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 2; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `stripmine_second_level_schedule_after_env_eval` (line 5155; span 64, body 62)

- **Responsibility:** Computes the target timestamp produced by ordinary, grouped second-level, or interleaved strip-mining after an environment prefix.
- **Why long:** Each proof repeats lifted-schedule evaluation, exact-column bookkeeping, and prefix/band/suffix splitting; layout-specific ordering remains real content.
- **Refactor:** Factor private lifted-schedule and identity-block evaluation packages, then keep the three layout theorems explicit specializations.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `stripmine_second_level_schedule_interleaved_after_env_eval` (line 5235; span 101, body 99)

- **Responsibility:** Computes the target timestamp produced by ordinary, grouped second-level, or interleaved strip-mining after an environment prefix.
- **Why long:** Each proof repeats lifted-schedule evaluation, exact-column bookkeeping, and prefix/band/suffix splitting; layout-specific ordering remains real content.
- **Refactor:** Factor private lifted-schedule and identity-block evaluation packages, then keep the three layout theorems explicit specializations.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `infer_pinstr_tiling_band_bound` (line 5499; span 48, body 46)

- **Responsibility:** Proves that an inferred ordinary or second-level schedule block lies within the schedule.
- **Why long:** Both proofs replay the same successful find/block-fit argument with different recognizers.
- **Refactor:** Add a private generic find_schedule_block_start_fit lemma; retain the two public specializations.
- **Order/risk:** `P0.3 duplicated bounds` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `infer_pinstr_second_level_band_bound` (line 5662; span 35, body 33)

- **Responsibility:** Proves that an inferred ordinary or second-level schedule block lies within the schedule.
- **Why long:** Both proofs replay the same successful find/block-fit argument with different recognizers.
- **Refactor:** Add a private generic find_schedule_block_start_fit lemma; retain the two public specializations.
- **Order/risk:** `P0.3 duplicated bounds` / `low`.
- **Use:** internal callers 2; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `check_pprog_second_level_schedule_symmetricb_sound` (line 6024; span 32, body 30)

- **Responsibility:** Turns a successful whole-program symmetry boolean into its relational property.
- **Why long:** Nested forallb inversion and list traversal dominate; there is no difficult semantic step.
- **Refactor:** Use named true-inversion lemmas for the component checker; do not hide the traversal behind broad automation.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pinstr_list_second_level_schedule_zero_erasureb_sound` (line 6149; span 35, body 33)

- **Responsibility:** Shows that accepted pairs have matching zero masks after second-level schedule extraction.
- **Why long:** Routine list and boolean inversion is repeated for each successful branch.
- **Refactor:** Factor a pair-check forallb_true_inv helper local to the checker family.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `lex_compare_affine_product_remove_zero_same_mask` (line 6251; span 39, body 37)

- **Responsibility:** Shows that removing coordinates under a common zero mask preserves the relevant lexicographic comparison.
- **Why long:** The induction is mathematical and follows the mask/schedule lists.
- **Refactor:** Keep the induction as a named theory lemma; only reuse generic combine/nth helpers.
- **Order/risk:** `P1.6 retain theory core` / `medium`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `zero_erasure_second_level_schedule_layout_lex_equivalent` (line 6328; span 92, body 90)

- **Responsibility:** Connects the zero-erased schedule layout with the full second-level lexicographic order.
- **Why long:** Most length is schedule-row lookup and common-mask reconstruction around the core zero-erasure lemma.
- **Refactor:** Share the paired row-lookup package; leave the final layout equivalence theorem and its core argument visible.
- **Order/risk:** `P1.3 row lookup helper` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `check_pprog_second_level_schedule_directb_sound` (line 6427; span 32, body 30)

- **Responsibility:** Lifts successful per-instruction second-level schedule checks to the program property.
- **Why long:** Executable checker traversal and boolean inversion account for the proof size.
- **Refactor:** Use a named traversal-success inversion lemma; retain this public theorem unchanged.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 0; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

### ProjectedScheduleBridge

#### `project_pluto_band_component_ip_ext_new_sched_ge` (line 6966; span 38, body 36)

- **Responsibility:** Relates pointwise schedule comparison before and after selecting a Pluto band component.
- **Why long:** The iff proof duplicates both directional projection and restored-coordinate bookkeeping.
- **Refactor:** Derive both from one projection evaluation lemma and a single iff constructor; keep public statements intact.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 3; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `project_pluto_band_component_ip_ext_new_sched_ge_iff` (line 7312; span 102, body 100)

- **Responsibility:** Relates pointwise schedule comparison before and after selecting a Pluto band component.
- **Why long:** The iff proof duplicates both directional projection and restored-coordinate bookkeeping.
- **Refactor:** Derive both from one projection evaluation lemma and a single iff constructor; keep public statements intact.
- **Order/risk:** `P1.2 projection abstraction` / `medium`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `stripmined_reversal_implies_prefix_eq_and_band_lt` (line 7428; span 50, body 48)

- **Responsibility:** Extracts equal earlier coordinates and a strictly decreasing active band component from a target reversal.
- **Why long:** This is the central lexicographic argument for ordinary strip-mining.
- **Refactor:** Keep these proofs explicit and adjacent; improve local names only, with no aggressive genericization.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `stripmined_reversal_implies_decreasing_band_component` (line 7574; span 31, body 29)

- **Responsibility:** Extracts equal earlier coordinates and a strictly decreasing active band component from a target reversal.
- **Why long:** This is the central lexicographic argument for ordinary strip-mining.
- **Refactor:** Keep these proofs explicit and adjacent; improve local names only, with no aggressive genericization.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 4; qualified external uses 2; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `second_level_schedule_tile_block_pointwise_le_common_sizes` (line 7881; span 36, body 34)

- **Responsibility:** Establishes common tile-block bounds and lexicographic equivalence for grouped/interleaved second-level layouts.
- **Why long:** The proofs carry layout-specific index arithmetic; only their row-lookup prelude is repetitive.
- **Refactor:** Reuse paired row/evaluation facts but retain separate grouped and interleaved order lemmas.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `second_level_schedule_interleaved_tile_block_pointwise_le_common_sizes` (line 7973; span 36, body 34)

- **Responsibility:** Establishes common tile-block bounds and lexicographic equivalence for grouped/interleaved second-level layouts.
- **Why long:** The proofs carry layout-specific index arithmetic; only their row-lookup prelude is repetitive.
- **Refactor:** Reuse paired row/evaluation facts but retain separate grouped and interleaved order lemmas.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `symmetric_second_level_schedule_layout_lex_equivalent` (line 8166; span 33, body 31)

- **Responsibility:** Establishes common tile-block bounds and lexicographic equivalence for grouped/interleaved second-level layouts.
- **Why long:** The proofs carry layout-specific index arithmetic; only their row-lookup prelude is repetitive.
- **Refactor:** Reuse paired row/evaluation facts but retain separate grouped and interleaved order lemmas.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 3; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `retiled_old_band_old_pprog_eqdom_retiled_old_pprog` (line 8431; span 33, body 31)

- **Responsibility:** Builds an equality-of-domains witness for the retiled old program.
- **Why long:** The proof is mostly record/conjunction assembly and uses a goal-shape repeat-match tactic.
- **Refactor:** Replace goal-shape matching with explicit field/conjunction construction; keep theorem as compatibility API.
- **Order/risk:** `P0.2 goal-shape removal` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_from_after_member_nth_data_source` (line 8686; span 96, body 94)

- **Responsibility:** Recovers source instruction, before/after entries, and witness data for a flattened target member.
- **Why long:** The theorem packages several nested list-map nth inversions; later giant bridges invoke it twice.
- **Refactor:** Turn its result into a private composed_point_facts constructor/record used uniformly for both endpoints; keep the theorem itself unchanged.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 7; qualified external uses 12; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `tiling_schedule_stripmined_validate_correct_with_bands` (line 8819; span 93, body 91)

- **Responsibility:** Combines inferred bands and projected schedule facts with the older validate_tiling correctness theorem.
- **Why long:** The proof performs compatibility plumbing for a route not used by the current dispatcher.
- **Refactor:** Retain exact exported API in a clearly labeled legacy compatibility section; avoid spending P0 effort shortening its mathematical internals.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

### CommonBandDirectChecker

#### `make_pluto_band_component_guard_polys_bad_component_sound` (line 9052; span 64, body 62)

- **Responsibility:** Relates generated guard polynomials to a bad band component or to the concrete instruction point.
- **Why long:** Both proofs unfold the same guard construction and repeat affine evaluation/list alignment.
- **Refactor:** Factor the shared guard-evaluation skeleton, while leaving bad-component and point conclusions as separate public lemmas.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `make_pluto_band_component_guard_polys_point_sound` (line 9147; span 63, body 61)

- **Responsibility:** Relates generated guard polynomials to a bad band component or to the concrete instruction point.
- **Why long:** Both proofs unfold the same guard construction and repeat affine evaluation/list alignment.
- **Refactor:** Factor the shared guard-evaluation skeleton, while leaving bad-component and point conclusions as separate public lemmas.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `check_pinstr_list_pluto_permutable_band_component_via_validate_tiling_sound` (line 9883; span 102, body 100)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pinstr_list_pluto_permutable_band_components_sound_with_env_len` (line 10044; span 35, body 33)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pinstr_list_pluto_permutable_bands_component_sound` (line 10099; span 100, body 98)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pinstr_list_pluto_permutable_bands_components_sound` (line 10280; span 38, body 36)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pprog_pluto_permutable_tiling_bands_strong_via_validate_tiling_sound_with_env_len` (line 10341; span 52, body 50)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pprog_permutable_tiling_bands_via_validate_tiling_sound_with_lengths` (line 10417; span 240, body 238)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `checked_tiling_schedule_stripmined_validate_correct_same_ctxt_with_reordering_checker` (line 10715; span 113, body 111)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto` (line 10982; span 110, body 108)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `ordinary_pair_local_reversal_bridge_wf_with_env_len` (line 11131; span 738, body 736)

- **Responsibility:** Converts an ordinary or recognized second-level target reversal into a checked decreasing band component for a pair of flattened instances.
- **Why long:** Genuine layout/order reasoning is buried under duplicated endpoint provenance, env/point splitting, timestamp recovery, and tile-link evaluation for point 1 and point 2.
- **Refactor:** P0: construct composed_point_facts for each endpoint and a paired schedule-row package; retain the layout-specific monotonicity block in these public theorems.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 1; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len` (line 11917; span 59, body 57)

- **Responsibility:** Combines strong band permutability with the local ordinary reversal bridge to obtain reordering safety.
- **Why long:** Mostly instantiates generic program-wide reordering machinery and threads environment lengths.
- **Refactor:** Keep as a short public composition theorem after endpoint helper extraction; no theory redesign.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 1; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `second_level_local_reversal_bridge_by_layout_wf_with_env_len` (line 12004; span 596, body 594)

- **Responsibility:** Converts an ordinary or recognized second-level target reversal into a checked decreasing band component for a pair of flattened instances.
- **Why long:** Genuine layout/order reasoning is buried under duplicated endpoint provenance, env/point splitting, timestamp recovery, and tile-link evaluation for point 1 and point 2.
- **Refactor:** P0: construct composed_point_facts for each endpoint and a paired schedule-row package; retain the layout-specific monotonicity block in these public theorems.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 2; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `infer_second_level_bands_compose_schedule1_nonempty` (line 12759; span 30, body 28)

- **Responsibility:** Shows the first composed schedule remains nonempty after successful second-level inference.
- **Why long:** Repeated option inversion and list nonemptiness facts, not mathematical complexity.
- **Refactor:** Derive from a named successful-inference inversion lemma.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `check_pprog_second_level_permutable_bands_via_validate_tiling_sound_with_env_len` (line 12800; span 83, body 81)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `tiling_sourceb_validate_correct_with_reordering` (line 12921; span 84, body 82)

- **Responsibility:** Combines source-shape validation and a supplied reordering-safety proof with tiling semantic correctness.
- **Why long:** The theorem assembles several already-proved interfaces and context equalities.
- **Refactor:** Preserve as the visible composition boundary; shorten only repeated context/equality setup.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 7; qualified external uses 5; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `checked_tiling_second_level_band_validate_correct_same_ctxt` (line 13018; span 33, body 31)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `checked_tiling_whole_program_permutability_validate_correct_same_ctxt` (line 13076; span 49, body 47)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 3; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto_wf` (line 13264; span 115, body 113)

- **Responsibility:** Carries component checks through the former general affine-validator fallback and same-context correctness wrappers.
- **Why long:** Large repeated program/list traversal and context plumbing remain, but none of these long proofs is reachable from a current runtime root.
- **Refactor:** Preserve every exported name/type as a wrapper and isolate the implementation in a labeled legacy section; refactor only after the direct path is clean.
- **Order/risk:** `P1.7 legacy isolation` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `flatten_instrs_ext_member_slice_local` (line 13583; span 50, body 48)

- **Responsibility:** Recovers membership in an instruction slice from flattened-list membership.
- **Why long:** Manual firstn/skipn/app and nth-error reasoning is generic list infrastructure.
- **Refactor:** Sink the generic slice lemma to Misc and keep this public local name as a wrapper.
- **Order/risk:** `P1.1 utility sinking` / `low`.
- **Use:** internal callers 4; qualified external uses 2; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `validate_two_instrs_pluto_band_component_direct_sound` (line 13643; span 79, body 77)

- **Responsibility:** Lifts a successful affine guard check from one instruction pair to a component, statement list, and whole program.
- **Why long:** The same collision-to-permutability argument and list traversal are specialized at four levels.
- **Refactor:** Introduce a private guarded_pair_validation_sound kernel plus a generic successful traversal lemma; retain all four public wrappers.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `validate_instr_list_pluto_band_component_direct_sound` (line 13748; span 82, body 80)

- **Responsibility:** Lifts a successful affine guard check from one instruction pair to a component, statement list, and whole program.
- **Why long:** The same collision-to-permutability argument and list traversal are specialized at four levels.
- **Refactor:** Introduce a private guarded_pair_validation_sound kernel plus a generic successful traversal lemma; retain all four public wrappers.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `check_pinstr_list_pluto_permutable_band_direct_sound` (line 13853; span 52, body 50)

- **Responsibility:** Lifts a successful affine guard check from one instruction pair to a component, statement list, and whole program.
- **Why long:** The same collision-to-permutability argument and list traversal are specialized at four levels.
- **Refactor:** Introduce a private guarded_pair_validation_sound kernel plus a generic successful traversal lemma; retain all four public wrappers.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len` (line 13919; span 52, body 50)

- **Responsibility:** Lifts a successful affine guard check from one instruction pair to a component, statement list, and whole program.
- **Why long:** The same collision-to-permutability argument and list traversal are specialized at four levels.
- **Refactor:** Introduce a private guarded_pair_validation_sound kernel plus a generic successful traversal lemma; retain all four public wrappers.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 0; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

### PerStatementBandChecker

#### `check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound` (line 14222; span 149, body 147)

- **Responsibility:** Proves the current componentwise checker establishes the program permutability property with statement-specific bands.
- **Why long:** The proof is a large but routine assembly of inferred-band lookup, component selection, pair validation, and list traversal.
- **Refactor:** Reuse the guarded-pair/traversal kernel while keeping statement-specific band lookup explicit; this current runtime theorem stays prominent.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 0; qualified external uses 3; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

### SemanticBandKernel

#### `make_semantic_band_component_guard_polys_bad_component_sound` (line 14560; span 47, body 45)

- **Responsibility:** Shows semantic-row guard polynomials characterize a bad active component.
- **Why long:** It repeats the affine guard evaluation skeleton from the ordinary direct checker with a different row source.
- **Refactor:** Parameterize the private guard-evaluation skeleton by row evidence; retain this theorem as the semantic specialization.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `validate_two_instrs_semantic_band_component_direct_sound` (line 14629; span 119, body 117)

- **Responsibility:** Turns successful semantic-row validation of one pair into permutability at the active component.
- **Why long:** Collision/access reasoning duplicates the ordinary and scalar-aware pair validators.
- **Refactor:** Reuse guarded_pair_validation_sound; keep semantic-row lookup and bad-component construction explicit.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `check_semantic_band_components_direct_sound` (line 14936; span 164, body 162)

- **Responsibility:** Lifts semantic pair validation across components, instructions, and the program.
- **Why long:** Nested list traversal and component selection dominate the body.
- **Refactor:** Factor one well-named traversal theorem parameterized by the pair checker, avoiding a broad recursive tactic.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 5; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

### ProgramWideSemanticReconstruction

#### `schedule_rows_of_links_aux_exact_cols` (line 15642; span 40, body 38)

- **Responsibility:** Proves rows recovered from tile links have the required source column count.
- **Why long:** A straightforward induction repeatedly projects exact-column evidence from link lookup.
- **Refactor:** Share a row-lookup/exact-cols record with second-level row evaluation; keep this theorem as the public list result.
- **Order/risk:** `P1.3 row lookup helper` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `schedule_lists_zero_erasure_match_pair_lex` (line 15962; span 55, body 53)

- **Responsibility:** Establishes lexicographic agreement of two schedule lists under their common erasure mask.
- **Why long:** The core list induction is real; surrounding nth/length facts overlap with earlier zero-erasure lemmas.
- **Refactor:** Retain the induction and reuse generic nth/combine plus common-mask helpers.
- **Order/risk:** `P1.6 retain theory core` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `infer_pprog_ordinary_semantic_band_shape_sound` (line 16091; span 61, body 59)

- **Responsibility:** Turns successful ordinary or second-level whole-program shape inference into its structural semantic property.
- **Why long:** Nested option matches, equality booleans, and list traversals are inverted repeatedly; the second-level property has more fields.
- **Refactor:** Add named success-inversion lemmas for constituent recognizers and rebuild the property explicitly.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `infer_pprog_second_level_semantic_band_shape_sound` (line 16194; span 169, body 167)

- **Responsibility:** Turns successful ordinary or second-level whole-program shape inference into its structural semantic property.
- **Why long:** Nested option matches, equality booleans, and list traversals are inverted repeatedly; the second-level property has more fields.
- **Refactor:** Add named success-inversion lemmas for constituent recognizers and rebuild the property explicitly.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `checked_tiling_sourceb_semantic_band_direct_true_inv` (line 16397; span 62, body 60)

- **Responsibility:** Extracts the selected semantic layout and checker evidence from a successful top-level semantic source check.
- **Why long:** Case analysis over dispatcher branches and option results accounts for the length.
- **Refactor:** Keep branch structure visible but use one true-inversion lemma per branch.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 2; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `semantic_stripmined_reversal_implies_decreasing_component` (line 16525; span 54, body 52)

- **Responsibility:** Derives a decreasing active semantic component from a reversed strip-mined target order.
- **Why long:** These are central lexicographic lemmas, with the second lifting pointwise comparison to list lex order.
- **Refactor:** Keep both as explicit theory lemmas; improve names/hypothesis grouping but do not collapse into automation.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 3; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `semantic_stripmined_reversal_implies_decreasing_component_lex` (line 16596; span 48, body 46)

- **Responsibility:** Derives a decreasing active semantic component from a reversed strip-mined target order.
- **Why long:** These are central lexicographic lemmas, with the second lifting pointwise comparison to list lex order.
- **Refactor:** Keep both as explicit theory lemmas; improve names/hypothesis grouping but do not collapse into automation.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `global_semantic_schedule_mask_zero_on_false` (line 16854; span 142, body 140)

- **Responsibility:** Proves every globally inactive semantic schedule slot evaluates to zero.
- **Why long:** The proof combines global slot indexing, padding, and per-statement schedule-row lookup in one induction.
- **Refactor:** Split into a slot-index lookup lemma and a padding-zero lemma, then compose them under the unchanged public theorem.
- **Order/risk:** `P1.3 row lookup helper` / `medium`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `semantic_ordinary_target_schedule_eval` (line 17175; span 30, body 28)

- **Responsibility:** Computes the ordinary target schedule from the reconstructed semantic rows.
- **Why long:** Only crosses the 30-line threshold because it opens the schedule package and column-size facts.
- **Refactor:** Reuse the lifted-schedule evaluation package; otherwise leave unchanged.
- **Order/risk:** `P1.3 evaluation scaffolding` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `ordinary_semantic_band_shape_reversal_bridge` (line 17518; span 1025, body 1014)

- **Responsibility:** Uses recognized program-wide semantic rows to turn any target reversal into an active decreasing component.
- **Why long:** The central argument is obscured by two copies of endpoint provenance, source/target timestamp reconstruction, mask lookup, and exact-column plumbing.
- **Refactor:** Use composed_point_facts plus a paired semantic_row_facts record; retain the ordinary semantic monotonicity core in this theorem.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `semantic_second_level_global_tile_block_local` (line 18629; span 75, body 73)

- **Responsibility:** Relates local second-level tile values to the globally reconstructed tile block and its pointwise order.
- **Why long:** Repeated lookup/padding arithmetic surrounds a genuine local-to-global relation.
- **Refactor:** Factor global-slot lookup facts, keeping the local-to-global theorem statements explicit.
- **Order/risk:** `P1.3 row lookup helper` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `semantic_second_level_global_tile_block_pointwise_le` (line 18753; span 42, body 40)

- **Responsibility:** Relates local second-level tile values to the globally reconstructed tile block and its pointwise order.
- **Why long:** Repeated lookup/padding arithmetic surrounds a genuine local-to-global relation.
- **Refactor:** Factor global-slot lookup facts, keeping the local-to-global theorem statements explicit.
- **Order/risk:** `P1.3 row lookup helper` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `semantic_second_level_target_schedule_eval` (line 18808; span 98, body 96)

- **Responsibility:** Computes the reconstructed second-level target timestamp, including global tile blocks and point rows.
- **Why long:** Repeated lifted schedule, padding, exact-column, and list-append evaluation scaffolding hides the layout formula.
- **Refactor:** Reuse evaluation and global-slot packages; keep the final target-layout equation visible.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `second_level_band_recipe_root_rows_exact_cols` (line 19062; span 33, body 31)

- **Responsibility:** Establishes exact column counts for recipe roots, ordinary/second-level semantic rows, and their composition.
- **Why long:** Four specializations repeat app/firstn/skipn exact-column bookkeeping; composed_semantic_rows_exact_cols also uses a goal-shape match.
- **Refactor:** Create low-level exact-cols firstn/skipn/app utilities and explicit constructors; replace the goal-shape match while retaining all public names.
- **Order/risk:** `P0.2 goal-shape and column utilities` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `second_level_semantic_rows_exact_cols` (line 19108; span 46, body 44)

- **Responsibility:** Establishes exact column counts for recipe roots, ordinary/second-level semantic rows, and their composition.
- **Why long:** Four specializations repeat app/firstn/skipn exact-column bookkeeping; composed_semantic_rows_exact_cols also uses a goal-shape match.
- **Refactor:** Create low-level exact-cols firstn/skipn/app utilities and explicit constructors; replace the goal-shape match while retaining all public names.
- **Order/risk:** `P0.2 goal-shape and column utilities` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `ordinary_semantic_rows_exact_cols` (line 19173; span 40, body 38)

- **Responsibility:** Establishes exact column counts for recipe roots, ordinary/second-level semantic rows, and their composition.
- **Why long:** Four specializations repeat app/firstn/skipn exact-column bookkeeping; composed_semantic_rows_exact_cols also uses a goal-shape match.
- **Refactor:** Create low-level exact-cols firstn/skipn/app utilities and explicit constructors; replace the goal-shape match while retaining all public names.
- **Order/risk:** `P0.2 goal-shape and column utilities` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `composed_semantic_rows_exact_cols` (line 19232; span 33, body 31)

- **Responsibility:** Establishes exact column counts for recipe roots, ordinary/second-level semantic rows, and their composition.
- **Why long:** Four specializations repeat app/firstn/skipn exact-column bookkeeping; composed_semantic_rows_exact_cols also uses a goal-shape match.
- **Refactor:** Create low-level exact-cols firstn/skipn/app utilities and explicit constructors; replace the goal-shape match while retaining all public names.
- **Order/risk:** `P0.2 goal-shape and column utilities` / `low`.
- **Use:** internal callers 4; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `second_level_semantic_band_shape_reversal_bridge` (line 19292; span 1336, body 1324)

- **Responsibility:** Uses recognized second-level semantic rows and tile recipes to turn any target reversal into an active decreasing component.
- **Why long:** This is the largest proof because endpoint reconstruction and schedule-row/tile-link facts are duplicated, then repeated again across grouped/interleaved layouts.
- **Refactor:** P0: package endpoint and paired semantic-row facts; after that, keep grouped/interleaved case arguments separate. Do not attempt a high-risk universal layout theorem now.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `ordinary_semantic_band_direct_reordering_safe` (line 20644; span 83, body 81)

- **Responsibility:** Combines semantic component-checker soundness and the matching reversal bridge into reordering safety.
- **Why long:** Most lines instantiate generic program-wide machinery and thread inferred shapes.
- **Refactor:** Keep as visible composition boundaries; shorten setup using the new fact packages.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `checked_tiling_sourceb_semantic_band_direct_ordinary_correct_same_ctxt` (line 20755; span 34, body 32)

- **Responsibility:** Connects accepted ordinary/second-level semantic routes and their dispatcher to same-context tiling correctness.
- **Why long:** Thin branch-specific composition wrappers just above the threshold.
- **Refactor:** Retain as public API; reuse a shared same-context composition helper only if it stays transparent.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `second_level_semantic_band_direct_reordering_safe` (line 20812; span 84, body 82)

- **Responsibility:** Combines semantic component-checker soundness and the matching reversal bridge into reordering safety.
- **Why long:** Most lines instantiate generic program-wide machinery and thread inferred shapes.
- **Refactor:** Keep as visible composition boundaries; shorten setup using the new fact packages.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `checked_tiling_sourceb_semantic_band_direct_second_correct_same_ctxt` (line 20924; span 34, body 32)

- **Responsibility:** Connects accepted ordinary/second-level semantic routes and their dispatcher to same-context tiling correctness.
- **Why long:** Thin branch-specific composition wrappers just above the threshold.
- **Refactor:** Retain as public API; reuse a shared same-context composition helper only if it stays transparent.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 0; qualified external uses 0; runtime reachable no; external-root reachable no. Exported by the functor but no qualified repository use and not runtime-reachable; preserve as compatibility API unless an intentional breaking change is approved.

#### `checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt` (line 20984; span 34, body 32)

- **Responsibility:** Connects accepted ordinary/second-level semantic routes and their dispatcher to same-context tiling correctness.
- **Why long:** Thin branch-specific composition wrappers just above the threshold.
- **Refactor:** Retain as public API; reuse a shared same-context composition helper only if it stays transparent.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 0; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

### ScalarAwareBands

#### `scalar_aware_prefix_gt_implies_active_decrease` (line 21364; span 68, body 66)

- **Responsibility:** Shows that a greater rendered prefix must expose a decreasing active non-scalar band component.
- **Why long:** This is the central mixed scalar/vector prefix argument.
- **Refactor:** Keep as explicit theory; only replace generic list arithmetic with named utilities.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `scalar_aware_stripmine_schedule_after_env_eval` (line 21496; span 147, body 145)

- **Responsibility:** Computes a strip-mined timestamp that interleaves constant scalar rows with active band rows.
- **Why long:** It repeats ordinary evaluation scaffolding and adds genuine scalar-mask rendering cases.
- **Refactor:** Reuse lifted/identity evaluation packages, while keeping scalar rendering cases explicit.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `make_schedule_rows_nondecreasing_poly_sound` (line 21711; span 37, body 35)

- **Responsibility:** Shows generated polynomial constraints enforce nondecreasing semantic schedule rows.
- **Why long:** Routine affine evaluation and list alignment dominate.
- **Refactor:** Reuse a generic affine-row guard evaluation helper.
- **Order/risk:** `P0.5 guarded-pair kernel` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `make_scalar_aware_band_component_guard_polys_bad_sound` (line 21853; span 125, body 123)

- **Responsibility:** Shows the scalar-aware guard encodes a bad active component plus scalar-prefix constraints.
- **Why long:** It duplicates ordinary/semantic affine guard plumbing and adds scalar-mask cases.
- **Refactor:** Parameterize the guard-evaluation skeleton; retain scalar-specific prefix obligations explicitly.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `validate_two_instrs_scalar_aware_band_component_direct_sound` (line 22014; span 128, body 126)

- **Responsibility:** Turns successful scalar-aware pair validation into the required component permutability fact.
- **Why long:** Access-collision reasoning duplicates the ordinary and semantic pair checkers.
- **Refactor:** Reuse guarded_pair_validation_sound with the scalar-aware guard theorem.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `check_pprog_scalar_aware_permutable_band_direct_sound` (line 22363; span 107, body 105)

- **Responsibility:** Lifts scalar-aware pair checks to the whole-program permutability property.
- **Why long:** Nested list/component traversal and shape lookup dominate.
- **Refactor:** Reuse generic pair-check traversal while leaving scalar shape lookup visible.
- **Order/risk:** `P0.5 guarded-pair kernel` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `check_scalar_aware_common_shape_entries_sound` (line 22639; span 38, body 36)

- **Responsibility:** Turns successful entry-level and whole-program scalar-aware shape inference into structural properties.
- **Why long:** Option/boolean/list inversion, not deep semantics, causes the length.
- **Refactor:** Add named success-inversion lemmas and reconstruct the property explicitly.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `infer_pprog_scalar_aware_common_shape_sound` (line 22712; span 31, body 29)

- **Responsibility:** Turns successful entry-level and whole-program scalar-aware shape inference into structural properties.
- **Why long:** Option/boolean/list inversion, not deep semantics, causes the length.
- **Refactor:** Add named success-inversion lemmas and reconstruct the property explicitly.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `render_scalar_aware_value_prefix_length` (line 22831; span 30, body 28)

- **Responsibility:** Computes the length of a rendered scalar-aware prefix.
- **Why long:** A small structural induction just crosses the long-proof threshold.
- **Refactor:** Keep or move beside the rendering definition; no abstraction is needed beyond clearer cases.
- **Order/risk:** `P1.5 local cleanup` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `scalar_aware_reversal_implies_mixed_gt` (line 22868; span 43, body 41)

- **Responsibility:** Relates a target reversal to mixed-prefix order and identifies an active component from unequal band values.
- **Why long:** The proofs contain real case analysis on scalar masks and lexicographic order.
- **Refactor:** Keep as explicit theory lemmas; reuse only generic nth/combine utilities.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `scalar_aware_component_active_from_band_values` (line 22973; span 72, body 70)

- **Responsibility:** Relates a target reversal to mixed-prefix order and identifies an active component from unequal band values.
- **Why long:** The proofs contain real case analysis on scalar masks and lexicographic order.
- **Refactor:** Keep as explicit theory lemmas; reuse only generic nth/combine utilities.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `scalar_aware_pair_local_reversal_bridge_wf_with_env_len` (line 23087; span 773, body 771)

- **Responsibility:** Converts a scalar-aware target reversal into the decreasing checked component needed for pair permutability.
- **Why long:** Two endpoint reconstructions and schedule evaluation packages obscure the scalar-aware prefix argument.
- **Refactor:** Use composed_point_facts and paired row facts; retain the scalar-prefix case split as the theorem core.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 1; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

#### `scalar_aware_common_shape_reversal_bridge` (line 23914; span 115, body 113)

- **Responsibility:** Instantiates the pair-local scalar-aware bridge from a common inferred program shape.
- **Why long:** Mostly shape lookup and argument transport into the much larger local bridge.
- **Refactor:** Keep as the program-shape boundary; simplify with a named shape-entry lookup lemma.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `checked_tiling_sourceb_scalar_aware_direct_reordering_safe` (line 24089; span 65, body 63)

- **Responsibility:** Combines scalar-aware checker soundness, inferred common shape, and reversal bridge into reordering safety.
- **Why long:** Composition and dispatcher evidence dominate the body.
- **Refactor:** Retain as a visible route-level theorem; share only generic composition setup.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

### PhaseAwareSemanticBands

#### `infer_pprog_phase_semantic_ordinary_band_shape_sound` (line 24951; span 58, body 56)

- **Responsibility:** Turns successful ordinary or second-level phase-aware shape inference into its semantic layout property.
- **Why long:** Nested recognizer-success inversion and list traversal dominate.
- **Refactor:** Reuse named recognizer inversion lemmas from the non-phase semantic route and keep phase fields explicit.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `infer_pprog_phase_semantic_second_level_band_shape_sound` (line 25016; span 61, body 59)

- **Responsibility:** Turns successful ordinary or second-level phase-aware shape inference into its semantic layout property.
- **Why long:** Nested recognizer-success inversion and list traversal dominate.
- **Refactor:** Reuse named recognizer inversion lemmas from the non-phase semantic route and keep phase fields explicit.
- **Order/risk:** `P1.4 checker inversion` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `render_scalar_aware_value_prefix_pointwise_le` (line 25210; span 35, body 33)

- **Responsibility:** Shows pointwise order is preserved by scalar-aware prefix rendering.
- **Why long:** A direct list/mask induction with routine arithmetic.
- **Refactor:** Keep as a small theory helper; reuse generic combine/nth lemmas.
- **Order/risk:** `P1.5 local cleanup` / `low`.
- **Use:** internal callers 2; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_added_tiles_eq` (line 25257; span 107, body 105)

- **Responsibility:** Identifies the added tile-coordinate block for ordinary and second-level phase layouts.
- **Why long:** The second-level proof repeats padding, quotient, and row-evaluation setup for several phase blocks.
- **Refactor:** Factor first-level padding/quotient and evaluated-identity-block helpers; retain separate ordinary/second-level equations.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_padded_identity_rows_from_eval` (line 25397; span 31, body 29)

- **Responsibility:** Evaluates phase-aware padded identity rows from a suffix or at one coordinate.
- **Why long:** Generic firstn/skipn/nth arithmetic is specialized locally.
- **Refactor:** Sink the generic padded-identity evaluation lemma to affine utilities and preserve these wrappers.
- **Order/risk:** `P1.1 utility sinking` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_ordinary_target_schedule_eval` (line 25440; span 65, body 63)

- **Responsibility:** Computes ordinary or second-level phase-aware target timestamps.
- **Why long:** Repeated lifted-schedule, padding, exact-column, and append-evaluation scaffolding surrounds the actual phase layout.
- **Refactor:** Reuse evaluation packages and phase tile identities; keep the final layout equations explicit.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_padded_identity_rows_at_eval` (line 25528; span 33, body 31)

- **Responsibility:** Evaluates phase-aware padded identity rows from a suffix or at one coordinate.
- **Why long:** Generic firstn/skipn/nth arithmetic is specialized locally.
- **Refactor:** Sink the generic padded-identity evaluation lemma to affine utilities and preserve these wrappers.
- **Order/risk:** `P1.1 utility sinking` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_second_level_target_schedule_eval` (line 25594; span 169, body 167)

- **Responsibility:** Computes ordinary or second-level phase-aware target timestamps.
- **Why long:** Repeated lifted-schedule, padding, exact-column, and append-evaluation scaffolding surrounds the actual phase layout.
- **Refactor:** Reuse evaluation packages and phase tile identities; keep the final layout equations explicit.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_second_schedules_equivalent_pair_lex` (line 25939; span 84, body 82)

- **Responsibility:** Shows the two reconstructed second-level phase schedules induce the same pairwise lexicographic comparison.
- **Why long:** The core equivalence is real; schedule lookup and padding facts account for much of the body.
- **Refactor:** Reuse paired row/evaluation packages but retain the equivalence proof as theory.
- **Order/risk:** `P1.6 retain theory core` / `high`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_second_added_tiles_eq` (line 26167; span 215, body 213)

- **Responsibility:** Identifies the added tile-coordinate block for ordinary and second-level phase layouts.
- **Why long:** The second-level proof repeats padding, quotient, and row-evaluation setup for several phase blocks.
- **Refactor:** Factor first-level padding/quotient and evaluated-identity-block helpers; retain separate ordinary/second-level equations.
- **Order/risk:** `P1.3 evaluation scaffolding` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_ordinary_band_shape_reversal_bridge` (line 26434; span 905, body 896)

- **Responsibility:** Converts a phase-aware ordinary or second-level target reversal into a decreasing checked semantic component.
- **Why long:** Both proofs duplicate endpoint provenance, phase schedule evaluation, padded-row lookup, and active-component selection; the layout-specific phase order is genuine.
- **Refactor:** Use composed_point_facts and paired phase_row_facts; retain ordinary and second-level phase arguments separately.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_second_level_band_shape_reversal_bridge` (line 27355; span 997, body 986)

- **Responsibility:** Converts a phase-aware ordinary or second-level target reversal into a decreasing checked semantic component.
- **Why long:** Both proofs duplicate endpoint provenance, phase schedule evaluation, padded-row lookup, and active-component selection; the layout-specific phase order is genuine.
- **Refactor:** Use composed_point_facts and paired phase_row_facts; retain ordinary and second-level phase arguments separately.
- **Order/risk:** `P0.4 endpoint fact package` / `medium`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_ordinary_band_direct_reordering_safe` (line 28364; span 77, body 75)

- **Responsibility:** Combines the phase semantic checker with the matching reversal bridge to obtain reordering safety.
- **Why long:** Most lines instantiate generic route-level correctness and thread inferred shape evidence.
- **Refactor:** Keep as visible route boundaries; share generic composition setup only.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `phase_semantic_second_level_band_direct_reordering_safe` (line 28464; span 82, body 80)

- **Responsibility:** Combines the phase semantic checker with the matching reversal bridge to obtain reordering safety.
- **Why long:** Most lines instantiate generic route-level correctness and thread inferred shape evidence.
- **Refactor:** Keep as visible route boundaries; share generic composition setup only.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 1; qualified external uses 0; runtime reachable yes; external-root reachable yes. No direct qualified external use, but transitive runtime proof-path dependency; preserve public name and type.

#### `checked_tiling_sourceb_phase_semantic_band_direct_correct_same_ctxt` (line 28569; span 57, body 55)

- **Responsibility:** Connects the selected phase-aware route to same-context tiling correctness.
- **Why long:** Dispatcher case analysis and composition facts cause the modest length.
- **Refactor:** Retain public entry theorem; use branch true-inversion helpers.
- **Order/risk:** `P0.6 direct composition` / `low`.
- **Use:** internal callers 0; qualified external uses 1; runtime reachable yes; external-root reachable yes. Direct qualified repository use; preserve public name and type.

## Utility placement and interface rule

- `ParallelCore`: schedule-only equality/permutability lemmas already live here; the local copies should be wrappers.
- `Misc` or a new low-level list utility: nth/combine membership, firstn/skipn/app, slicing, and Sorted-filter transport. Do not introduce dependencies from this validator into ISS or code-generation modules merely to reuse a duplicate lemma.
- `PolyBase`/low-level affine utility: affine-product app/firstn/skipn evaluation, identity-row evaluation, padded identity rows, and exact-column closure. Existing identical app lemmas in higher-level modules should eventually also use this sink.
- Private helper records in this file or a validator-private utility: `composed_point_facts`, paired semantic-row facts, successful recognizer inversions, and guarded-pair validation. These encode proof plumbing, not a new public theory API.
- Public API invariant: do not rename, delete, move, or change the type of any existing declaration. If an implementation moves, leave the original declaration as a qualified wrapper.
