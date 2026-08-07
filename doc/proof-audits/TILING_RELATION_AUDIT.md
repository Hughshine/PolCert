# TilingRelation.v declaration and proof audit

Generated from `src/TilingRelation.v` in the `proof/readability-cleanup` worktree.
This is a lexical call/use audit with Coq comments removed.  “Qualified external” means a current-repository dotted use ending in the declaration name (for example `Tiling.foo`, `Base.Tiling.foo`, or `TileRel.foo`).  “Public closure” is the transitive dependency closure of those roots inside this file.  It is a conservative repository-usage measure, not permission to delete an exported declaration.

## Inventory

- Source size: 8,389 lines.
- Declarations: 221; all 221 are externally visible (none is `Local`).
- Proofs: 161; proofs with at least 30 proof lines: 47.
- Qualified external sites: 1,012 over 48 directly used declarations.
- Public dependency closure: 159 declarations; 62 exported declarations are outside it.
- External sites by file: `TilingBandScheduleValidator.v` 777, `TilingBandMixedSecondValidator.v` 131, `TilingBoolChecker.v` 34, `TilingBandPhaseScalarValidator.v` 30, `TilingValidator.v` 17, `TilingCanonicalScheduleValidator.v` 17, `TilingBandDirectRuntime.v` 4, `ISSCutSemantics.v` 2.

The exact external sites, internal caller names, internal dependencies, tactic counts, spans, and closure bits for every declaration are in `/tmp/tiling_relation_declarations.csv`.

## Long proofs (all proofs >=30 lines read)

| declaration | span | proof lines | role | why long | low-risk action |
|---|---:|---:|---|---|---|
| `tiling_rel_pinstr_list_app_singleton_inv` | 528-570 | 35 | legacy relation-list plumbing | Reverse decomposition of three lock-step lists; duplicates the source variant. | Do not touch first. Later share a generic ternary-list suffix lemma, or leave with a phase comment if preserving definitional behavior is paramount. |
| `tiling_rel_pinstr_list_source_app_singleton_inv` | 572-614 | 35 | relation-list plumbing | Reverse decomposition of three lock-step lists; duplicates the compiled/general variant. | Add a named last-element split helper only after the source semantic chain is otherwise cleaned; changing the relation to a generic Forall3 is higher risk. |
| `eval_lower_link_affine_row_after_env` | 857-918 | 53 | core representation algebra | Manually reassociates four vector segments and bridges two dot-product implementations. | Keep here. Extract a Local dot-product split/reassociation helper shared with the upper-row proof; add a stage comment before coefficient splitting. |
| `eval_upper_link_affine_row_after_env` | 953-1022 | 61 | core representation algebra | Mirror of the lower-row proof plus negated coefficient algebra; repeats the same split twice. | Keep here. Reuse the same Local split helper and name the final arithmetic identity; no API change. |
| `compile_link_domain_after_env_from_sound` | 1113-1213 | 89 | core representation theorem | Induction over links carries a growing prefix; repeated suffix existence/length and app reassociation obscure the two constraint obligations. | After eval_tile_links_app_suffix, add a Local suffix-with-length lemma and a Local current-link-bounds lemma returning lower and upper constraints together. |
| `compile_link_domain_after_env_from_complete` | 1239-1326 | 75 | core representation theorem | Inverse induction peels two Boolean constraints and reconstructs the parent coordinate; list reassociation consumes much of the proof. | Add a Local canonical-vector reassociation lemma and name the one-link reconstruction step. Keep the induction and theorem in this file. |
| `tiling_rel_pinstr_structure_domain_lifted_compiled` | 1386-1435 | 35 | legacy compiled bridge | Unfolding a broad conjunction just to project the domain equality and rewrite the compiled witness. | Current public closure does not reach it. Defer; eventually derive from a small domain-projection helper. |
| `tiling_rel_pinstr_structure_source_domain_lifted` | 1463-1525 | 48 | core representation theorem | Unfolds the full source relation and manually rewrites lifted constraints. | Extract Local relation_domain_eq_source and reuse lifted_base_domain_after_env_in_poly; keep the public theorem as a short wrapper. |
| `tiling_rel_pinstr_structure_source_domain_complete` | 1566-1612 | 32 | core representation theorem | Inverse of domain_lifted; most lines project the same relation fields and normalize the witness. | Pair with the previous theorem through the same Local projection helper. This is externally used 18 times, so retain statement/path exactly. |
| `tiling_rel_pinstr_structure_source_transformation_lifted` | 1859-1931 | 63 | core payload bridge | The semantic fact is simple; computing current environment dimension through a tiled index creates two nested length assertions. | Add Local eval_pinstr_tiling_index_with_env_length/current_env_dim helper immediately before this theorem. |
| `sortedb_instr_point_np_implies_sorted_np` | 2537-2572 | 31 | generic/misplaced | Rebuilds strict Sorted from a Boolean selection-sort comparator and NoDupA. | Move the entire comparator block (2387-2572) to a shared InstrPointOrder functor; it is duplicated in ISSCutSemantics. Preserve TilingRelation names with wrappers/exports. |
| `before_of_retiled_old_point_old_of_compose_tiling_instr_point_ext` | 2618-2679 | 47 | legacy compiled bridge | Record equality is proved through repeated index-length and skipn normalization. | Unreachable from current public roots. Defer or isolate with the compiled route; comments are sufficient now. |
| `tiling_rel_pprog_structure_compiled_before_of_retiled_old_point_belongs_to_nth` | 2722-2838 | 88 | legacy compiled bridge | Reconstructs the same env/added/point decomposition used throughout the source route. | Defer. If retained, make it consume the same canonical-index helper as the source theorem. |
| `tiling_rel_pprog_structure_source_before_of_retiled_old_point_belongs_to_nth` | 2840-2980 | 112 | core erasure bridge | Reprojects the statement relation, synthesizes a retiled relation, splits the index, and invokes domain completeness. | Insert Local source_statement_retiled_old_relation plus Local canonical_retiled_old_index after tiled_index_split; the public theorem then only packages belongs_to fields. |
| `tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective` | 2982-3238 | 223 | core erasure representation theorem | Performs the complete env/added/point decomposition twice, then proves every record field separately (21 asserts). | Highest-yield helper extraction: canonical_retiled_old_index_source for one point. Then compare erased point, recover added coordinates functionally, and finish via a generic belongs_to_same_np/index lemma. |
| `before_ipl_from_retiled_old_forward_source` | 3240-3321 | 51 | core list bridge | Unpacks map membership and flatten membership, then reconstructs prefix/belongs/nth/length. | Keep as the named list-level adapter. It becomes short after the belongs_to and index-length helpers; add four field labels in a comment. |
| `tiling_rel_pinstr_structure_source_before_of_retiled_old_sched_le_iff` | 3323-3518 | 167 | currently unreachable source side branch | Contains two inline copies of timestamp preservation; the public timestamp theorem appears later. | Either move the timestamp theorem/helper before this proof and rewrite twice, or defer because no current public root reaches this theorem. |
| `before_ipl_from_retiled_old_forward` | 3596-3671 | 45 | legacy compiled bridge | Compiled analogue of forward_source. | Defer with the compiled route. |
| `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_point_injective` | 3673-3889 | 191 | legacy compiled bridge | Near-duplicate of the 223-line source injectivity proof. | Do not clean independently. Isolate or derive from a shared canonical-index helper only after the main source proof is stable. |
| `before_ipl_from_retiled_old_nodup` | 3891-3948 | 32 | legacy compiled bridge | Maps NoDup through compiled-route injectivity. | Defer. Generic NoDup_map_on should live in `ListExt`. |
| `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_time_stamp` | 3950-4041 | 78 | legacy compiled bridge | Canonical index split plus lifted schedule evaluation. | Defer; later share the timestamp core with source route. |
| `tiling_rel_pinstr_structure_source_before_of_retiled_old_time_stamp` | 4043-4138 | 79 | core schedule bridge | Canonical index split and skipn normalization are repeated from injectivity/belongs proofs. | Consume canonical_retiled_old_index_source and a Local tiled_point_part_app_exact helper; retain this public theorem because the final chain uses it. |
| `tiling_rel_pprog_structure_source_before_of_retiled_old_instr_semantics_iff_nth` | 4260-4454 | 164 | core semantic bridge | Recreates the retiled-old relation, index split, tile-coordinate completeness, identity-view equality, then executes the two semantic directions. | Split into Local source_statement_retiled_old_relation, Local retiled_old_index_realizes_source_point, and a final two-direction semantic wrapper. Add stage comments if helpers are not yet extracted. |
| `tiling_rel_pprog_structure_compiled_old_point_belongs_to_nth` | 4555-4645 | 67 | legacy compiled constructor | Long record belongs_to proof dominated by current-env-dimension arithmetic. | Defer; the proposed tiled-index length helper would shorten it automatically. |
| `tiling_rel_pprog_structure_compiled_before_point_has_retiled_old_preimage_nth` | 4647-4746 | 64 | legacy compiled constructor | Builds a canonical preimage then proves record extensionality field by field. | Defer/isolate with compiled route. |
| `before_ipl_from_retiled_old_backward` | 4748-4878 | 100 | legacy compiled list bridge | Combines canonical preimage with flatten membership; repeats index length arithmetic. | Defer/isolate with compiled route. |
| `tiling_rel_pprog_structure_source_before_point_has_retiled_old_preimage_nth` | 4952-5089 | 103 | core erasure completeness | Builds the tiled preimage and normalizes index, timestamp, transformation, instruction, and depth. | Extract Local source_point_canonical_preimage after the one-point belongs theorem; use record extensionality or the generic belongs_to functional lemma. |
| `before_ipl_from_retiled_old_backward_source` | 5091-5201 | 80 | core list bridge | Uses the preimage theorem but manually rebuilds the flatten membership certificate, especially its index-length field. | Add Local retiled_old_point_flatten_certificate; leave this theorem as the list-level completeness adapter. |
| `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists` | 5217-5364 | 119 | legacy compiled sorting bridge | Builds SelectionSort output, membership iff, NoDupA, and sortedness. | Current public closure does not reach it. Defer. |
| `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm` | 5366-5534 | 140 | legacy compiled sorting bridge | Duplicates the entire preceding 119-line theorem to add a Permutation conclusion. | Low-risk collapse: call the preceding exists theorem, rewrite its equality, and use selection_sort_perm. This removes about 100 proof lines without changing statements. |
| `tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth` | 5536-5622 | 61 | legacy compiled constructor | Target-point belongs proof plus current-env-dimension arithmetic. | Defer; reuse tiled-index length helper if retained. |
| `compose_tiling_instr_point_ext_from_after_belongs_to_ext` | 5790-5835 | 37 | core target/intermediate bridge | Unfolds seven records/predicates and proves current environment dimension from target depth. | Add Local current_env_dim_of_after_point. The semantic content belongs here. |
| `tiling_rel_pprog_structure_compiled_retiled_old_eqdom` | 5988-6058 | 60 | legacy compiled program bridge | Projects program relation, reproves builder length, and creates rel_list eqdom. | Unreachable. Defer or isolate with compiled route. |
| `flatten_instr_nth_after_implies_flatten_instr_nth_retiled_old` | 6227-6297 | 63 | core list representation theorem | Transports the four flatten fields across a point map; membership has forward/backward inverse cases. | Keep here. Add four stage comments; optional generic flatten_instr_nth_map helper belongs in PolyLang, not TilingRelation. |
| `flatten_instr_nth_after_implies_flatten_instr_nth_tiling_ext` | 6299-6388 | 82 | core list representation theorem | Same four-field transport for extended points; backward membership contains an inline new_of_ext belongs_to conversion. | Extract Local new_of_ext_belongs_to_after from belongs_to_ext and reuse it; otherwise stage comments are enough. |
| `flatten_instrs_after_implies_tiling_ext_exists` | 6507-6691 | 167 | core program representation theorem | Reverse induction aligns before/after/witness lists and simultaneously constructs normal and extended flattened lists. | Keep the theorem. Extract generic last-element/list-length split helpers; annotate base, split, per-statement lift, and append stages. |
| `flatten_instrs_retiled_old_implies_before_exists_perm` | 6693-6933 | 212 | legacy compiled whole-program bridge | Reverse induction and append bookkeeping; near-duplicate of the 228-line source theorem. | Unreachable. Do not refactor first; isolate with compiled route. |
| `tiling_after_to_retiled_old_poly_correct` | 6935-7056 | 97 | core semantic reordering theorem | Constructs extended instances, sorts by old timestamps, applies stable-permutation semantics, and repackages PolyPointListSema. | Keep intact structurally. Add comments for the four semantic stages; helper extraction would hide the main argument rather than clarify it. |
| `flatten_instrs_retiled_old_member_nth_data` | 7058-7198 | 105 | legacy compiled metadata bridge | Recovers aligned before/after/witness nth entries from one flattened member. | Unreachable. Defer; source version is the active one. |
| `before_ipl_from_retiled_old_nodup_source` | 7200-7261 | 36 | core list bridge | Maps NoDup using one-point injectivity. | Short enough after canonical injectivity is cleaned. Replace the local generic NoDup lemma with a `ListExt` theorem while keeping a compatibility wrapper. |
| `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_source` | 7263-7410 | 119 | source sorting constructor, currently only duplicated | Builds sorted source instances and establishes all flatten fields. | Retain as the single implementation theorem; make the following permutation theorem call it. |
| `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm_source` | 7412-7580 | 140 | core source sorting bridge | Duplicates all 119 lines of the preceding theorem merely to expose Permutation. | Highest-confidence low-risk rewrite: invoke exists_source, use its defining equality, then selection_sort_perm. Preserve name and statement. |
| `flatten_instrs_retiled_old_member_nth_data_source` | 7582-7724 | 107 | core metadata bridge | Finds aligned nth entries through length bounds and packs ten facts in nested conjunctions. | Keep as the named metadata bundle. Extract a generic aligned-map3 nth helper if desired; use a local record only if it materially improves callers. |
| `flatten_instrs_retiled_old_member_time_stamp_preserved_source` | 7785-7852 | 42 | core program schedule adapter | Unpacks the metadata bundle and delegates to the one-statement timestamp theorem. | Already well factored; add a one-line stage comment only. |
| `flatten_instrs_retiled_old_implies_before_exists_perm_source` | 7854-8108 | 228 | core whole-program representation theorem | Reverse induction aligns three lists, converts the last statement, transports head/tail maps, and appends permutations. | Keep. Add four phase comments and extract only last-element/nth bookkeeping helpers; avoid hiding the induction invariant. |
| `tiling_retiled_old_to_before_poly_correct_with_env_len_source` | 8110-8207 | 68 | core final semantic bridge | Combines flattened-list representation, per-point semantic preservation, schedule preservation, and permutation into PolyPointListSema. | Keep as the visible source-recovery theorem. Add comments naming these four obligations; generic map-semantics/sorted-map lemmas should move out. |
| `tiling_retiled_old_to_before_instance_correct_source` | 8209-8277 | 42 | final wrapper | Lifts the polyhedral theorem through initial environment length and instance_list_semantics. | Keep. Its length is mostly the semantic constructor and is readable after a two-stage comment. |

## Cleanup Applied After the Baseline

The highest-confidence item above is now implemented without changing the
public theorem statement.  The `...exists_perm_source` theorem calls the
preceding stronger `...exists_source` theorem and derives the additional
permutation result from `selection_sort_perm`; its former duplicated
sorting, membership, `NoDupA`, and `Sorted` reconstruction has been removed.

## Every declaration

`callers` is the number of declarations in this file that refer to the name.  `ext` is the number of qualified external sites.  Exact names/sites are in the CSV.

| group | declaration | kind | span | total | proof | callers | ext | root | closure |
|---|---|---|---:|---:|---:|---:|---:|---|---|
| A: representation builders | `lift_constraint_after_env` | Definition | 35-37 | 3 | 0 | 6 | 4 | True | True |
| A: representation builders | `lift_affine_function_after_env` | Definition | 39-41 | 3 | 0 | 4 | 8 | True | True |
| A: representation builders | `identity_affine_row` | Definition | 43-45 | 3 | 0 | 1 | 7 | True | True |
| A: representation builders | `identity_affine_rows_from` | Fixpoint | 47-54 | 8 | 0 | 2 | 15 | True | True |
| A: representation builders | `pad_transformation_after_env` | Definition | 56-66 | 11 | 0 | 1 | 2 | True | True |
| A: representation builders | `lift_access_after_env` | Definition | 68-71 | 4 | 0 | 2 | 0 | False | True |
| A: representation builders | `lift_schedule_after_env` | Definition | 73-75 | 3 | 0 | 8 | 77 | True | True |
| A: representation builders | `pinstr_tiling_witness` | Record | 77-81 | 5 | 0 | 15 | 0 | False | True |
| A: representation builders | `wf_pinstr_tiling_witness` | Definition | 83-84 | 2 | 0 | 12 | 0 | False | True |
| A: representation builders | `wf_statement_tiling_witness_with_param_dim` | Definition | 86-92 | 7 | 0 | 39 | 45 | True | True |
| A: representation builders | `app_singleton_cons` | Lemma | 94-103 | 10 | 7 | 1 | 0 | False | True |
| A: representation builders | `NoDup_map_on` | Lemma | 105-137 | 33 | 24 | 2 | 7 | True | True |
| A: representation builders | `Forall_nth_error` | Lemma | 139-149 | 11 | 6 | 3 | 56 | True | True |
| A: representation builders | `Forall2_nth_error` | Lemma | 151-167 | 17 | 11 | 2 | 7 | True | True |
| A: representation builders | `nth_error_map_some` | Lemma | 169-180 | 12 | 8 | 7 | 46 | True | True |
| A: representation builders | `eval_pinstr_tiling_index_with_env` | Definition | 182-184 | 3 | 0 | 23 | 0 | False | True |
| A: representation builders | `compile_ge_affine_row_to_constraint` | Definition | 186-187 | 2 | 0 | 4 | 0 | False | True |
| A: representation builders | `lower_link_affine_row_after_env` | Definition | 189-199 | 11 | 0 | 3 | 0 | False | True |
| A: representation builders | `upper_link_affine_row_after_env` | Definition | 201-211 | 11 | 0 | 3 | 0 | False | True |
| A: representation builders | `lower_link_constraint_after_env` | Definition | 213-216 | 4 | 0 | 4 | 0 | False | True |
| A: representation builders | `upper_link_constraint_after_env` | Definition | 218-221 | 4 | 0 | 4 | 0 | False | True |
| A: representation builders | `compile_link_domain_after_env_from` | Fixpoint | 223-231 | 9 | 0 | 4 | 0 | False | True |
| A: representation builders | `compile_link_domain_after_env` | Definition | 233-235 | 3 | 0 | 4 | 0 | False | True |
| A: representation builders | `lifted_base_domain_after_env` | Definition | 237-241 | 5 | 0 | 7 | 3 | True | True |
| A: representation builders | `lifted_accesses_after_env` | Definition | 243-248 | 6 | 0 | 3 | 2 | True | True |
| B: declarative relations/list shape | `tiling_rel_pinstr_structure` | Definition | 250-269 | 20 | 0 | 9 | 1 | True | True |
| B: declarative relations/list shape | `tiling_rel_pinstr_structure_source` | Definition | 271-288 | 18 | 0 | 19 | 34 | True | True |
| B: declarative relations/list shape | `source_view_of_tiled_pinstr` | Definition | 290-303 | 14 | 0 | 2 | 0 | False | False |
| B: declarative relations/list shape | `source_view_of_tiled_pinstrs` | Fixpoint | 305-314 | 10 | 0 | 2 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pinstr_list` | Fixpoint | 316-326 | 11 | 0 | 6 | 1 | True | True |
| B: declarative relations/list shape | `tiling_rel_pinstr_list_source` | Fixpoint | 328-338 | 11 | 0 | 5 | 3 | True | True |
| B: declarative relations/list shape | `tiling_rel_pprog_structure` | Definition | 340-347 | 8 | 0 | 5 | 1 | True | True |
| B: declarative relations/list shape | `tiling_rel_pprog_structure_source` | Definition | 349-356 | 8 | 0 | 18 | 42 | True | True |
| B: declarative relations/list shape | `witness_matches_compiled_link_domain` | Definition | 358-360 | 3 | 0 | 4 | 0 | False | True |
| B: declarative relations/list shape | `compiled_pinstr_tiling_witness` | Definition | 362-368 | 7 | 0 | 42 | 128 | True | True |
| B: declarative relations/list shape | `source_view_of_tiled_pprog` | Definition | 370-380 | 11 | 0 | 0 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pinstr_structure_compiled` | Definition | 382-387 | 6 | 0 | 15 | 2 | True | True |
| B: declarative relations/list shape | `current_src_transformation_of_pinstr` | Definition | 389-391 | 3 | 0 | 6 | 1 | True | True |
| B: declarative relations/list shape | `compose_tiling_pinstr_ext` | Definition | 393-408 | 16 | 0 | 9 | 76 | True | True |
| B: declarative relations/list shape | `retiled_old_pinstr` | Definition | 410-424 | 15 | 0 | 40 | 7 | True | True |
| B: declarative relations/list shape | `compose_tiling_instr_point_ext` | Definition | 426-449 | 24 | 0 | 7 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pprog_structure_compiled` | Definition | 451-454 | 4 | 0 | 20 | 2 | True | True |
| B: declarative relations/list shape | `tiling_rel_pinstr_list_lengths` | Lemma | 456-470 | 15 | 10 | 3 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pinstr_list_source_lengths` | Lemma | 472-486 | 15 | 10 | 2 | 6 | True | True |
| B: declarative relations/list shape | `tiling_rel_pprog_structure_compiled_lengths` | Lemma | 488-509 | 22 | 14 | 2 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pprog_structure_source_lengths` | Lemma | 511-526 | 16 | 8 | 2 | 3 | True | True |
| B: declarative relations/list shape | `tiling_rel_pinstr_list_app_singleton_inv` | Lemma | 528-570 | 43 | 35 | 1 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pinstr_list_source_app_singleton_inv` | Lemma | 572-614 | 43 | 35 | 1 | 0 | False | True |
| B: declarative relations/list shape | `tiling_rel_pprog_structure_compiled_app_singleton_inv` | Lemma | 616-647 | 32 | 20 | 1 | 0 | False | False |
| B: declarative relations/list shape | `tiling_rel_pprog_structure_source_app_singleton_inv` | Lemma | 649-678 | 30 | 18 | 1 | 0 | False | True |
| B: declarative relations/list shape | `Forall2_app_singleton_inv` | Lemma | 680-699 | 20 | 16 | 3 | 0 | False | True |
| C: link-domain representation | `lift_affine_function_after_env_eval` | Lemma | 701-719 | 19 | 11 | 6 | 37 | True | True |
| C: link-domain representation | `wf_compiled_pinstr_tiling_witness` | Lemma | 721-729 | 9 | 6 | 7 | 18 | True | True |
| C: link-domain representation | `compiled_pinstr_tiling_witness_matches` | Lemma | 731-740 | 10 | 6 | 4 | 18 | True | True |
| C: link-domain representation | `lift_access_after_env_exact_cell` | Lemma | 742-753 | 12 | 6 | 2 | 0 | False | False |
| C: link-domain representation | `lift_constraint_after_env_satisfies` | Lemma | 755-776 | 22 | 14 | 1 | 0 | False | True |
| C: link-domain representation | `tiling_dot_product_eq_linalg_dot_product` | Lemma | 778-789 | 12 | 9 | 3 | 5 | True | True |
| C: link-domain representation | `compile_ge_affine_row_to_constraint_sound` | Lemma | 791-817 | 27 | 20 | 2 | 0 | False | True |
| C: link-domain representation | `compile_ge_affine_row_to_constraint_complete` | Lemma | 819-845 | 27 | 20 | 2 | 0 | False | True |
| C: link-domain representation | `tiling_dot_product_mult_left` | Lemma | 847-855 | 9 | 5 | 1 | 0 | False | True |
| C: link-domain representation | `eval_lower_link_affine_row_after_env` | Lemma | 857-918 | 62 | 53 | 2 | 0 | False | True |
| C: link-domain representation | `lower_link_affine_row_after_env_sound` | Lemma | 920-934 | 15 | 6 | 1 | 0 | False | True |
| C: link-domain representation | `lower_link_constraint_after_env_sound` | Lemma | 936-951 | 16 | 7 | 1 | 0 | False | True |
| C: link-domain representation | `eval_upper_link_affine_row_after_env` | Lemma | 953-1022 | 70 | 61 | 2 | 0 | False | True |
| C: link-domain representation | `upper_link_affine_row_after_env_sound` | Lemma | 1024-1038 | 15 | 6 | 1 | 0 | False | True |
| C: link-domain representation | `upper_link_constraint_after_env_sound` | Lemma | 1040-1055 | 16 | 7 | 1 | 0 | False | True |
| C: link-domain representation | `lower_link_constraint_after_env_complete` | Lemma | 1057-1074 | 18 | 9 | 1 | 0 | False | True |
| C: link-domain representation | `upper_link_constraint_after_env_complete` | Lemma | 1076-1093 | 18 | 9 | 1 | 0 | False | True |
| C: link-domain representation | `eval_tile_links_app_suffix` | Lemma | 1095-1111 | 17 | 13 | 1 | 0 | False | True |
| C: link-domain representation | `compile_link_domain_after_env_from_sound` | Lemma | 1113-1213 | 101 | 89 | 1 | 0 | False | True |
| C: link-domain representation | `compile_link_domain_after_env_sound` | Theorem | 1215-1237 | 23 | 15 | 2 | 0 | False | True |
| C: link-domain representation | `compile_link_domain_after_env_from_complete` | Theorem | 1239-1326 | 88 | 75 | 1 | 0 | False | True |
| C: link-domain representation | `compile_link_domain_after_env_complete` | Theorem | 1328-1350 | 23 | 13 | 2 | 0 | False | True |
| C: link-domain representation | `lifted_base_domain_after_env_in_poly` | Lemma | 1352-1367 | 16 | 8 | 5 | 0 | False | True |
| C: link-domain representation | `tiling_rel_pinstr_structure_domain_decompose` | Theorem | 1369-1384 | 16 | 9 | 0 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_structure_domain_lifted_compiled` | Theorem | 1386-1435 | 50 | 35 | 1 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_structure_compiled_domain_lifted` | Theorem | 1437-1461 | 25 | 11 | 4 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_structure_source_domain_lifted` | Theorem | 1463-1525 | 63 | 48 | 1 | 0 | False | True |
| C: link-domain representation | `tiling_rel_pinstr_structure_compiled_domain_complete` | Theorem | 1527-1564 | 38 | 25 | 4 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_structure_source_domain_complete` | Theorem | 1566-1612 | 47 | 32 | 3 | 18 | True | True |
| C: link-domain representation | `tiling_rel_pinstr_structure_compiled_index_complete` | Theorem | 1614-1640 | 27 | 13 | 0 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_structure_compiled_domain_iff` | Theorem | 1642-1668 | 27 | 14 | 1 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_list_compiled_nth` | Lemma | 1670-1691 | 22 | 14 | 1 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pinstr_list_source_nth` | Lemma | 1693-1713 | 21 | 14 | 1 | 0 | False | True |
| C: link-domain representation | `tiling_rel_pprog_structure_compiled_nth` | Theorem | 1715-1738 | 24 | 11 | 11 | 0 | False | False |
| C: link-domain representation | `tiling_rel_pprog_structure_source_nth` | Theorem | 1740-1761 | 22 | 9 | 7 | 16 | True | True |
| C: link-domain representation | `tiling_rel_pprog_structure_compiled_domain_iff_nth` | Theorem | 1763-1801 | 39 | 16 | 0 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_waccess_exact_cells` | Theorem | 1803-1822 | 20 | 10 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_raccess_exact_cells` | Theorem | 1824-1843 | 20 | 10 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_source_of_tiled` | Lemma | 1845-1857 | 13 | 8 | 0 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_source_transformation_lifted` | Theorem | 1859-1931 | 73 | 63 | 1 | 0 | False | True |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_source_instr_semantics_lifted_iff` | Theorem | 1933-1958 | 26 | 10 | 1 | 0 | False | True |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_waccess_lifted` | Theorem | 1960-1981 | 22 | 12 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_raccess_lifted` | Theorem | 1983-2004 | 22 | 12 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_compiled_waccess_lifted` | Theorem | 2006-2023 | 18 | 6 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_compiled_raccess_lifted` | Theorem | 2025-2042 | 18 | 6 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pprog_structure_compiled_waccess_lifted_nth` | Theorem | 2044-2081 | 38 | 16 | 0 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pprog_structure_compiled_raccess_lifted_nth` | Theorem | 2083-2119 | 37 | 15 | 0 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pinstr_structure_compiled_old_schedule_lifted` | Theorem | 2121-2141 | 21 | 10 | 1 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth` | Theorem | 2143-2180 | 38 | 17 | 0 | 0 | False | False |
| D: lifted payload/access facts | `tiling_rel_pprog_structure_compiled_belongs_to_ext_nth` | Theorem | 2182-2225 | 44 | 19 | 0 | 0 | False | False |
| E: erase tile coordinates | `tiled_added_part` | Definition | 2227-2229 | 3 | 0 | 10 | 36 | True | True |
| E: erase tile coordinates | `tiled_point_part` | Definition | 2231-2233 | 3 | 0 | 14 | 36 | True | True |
| E: erase tile coordinates | `before_index_of_retiled_old` | Definition | 2235-2237 | 3 | 0 | 14 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_point` | Definition | 2239-2251 | 13 | 0 | 20 | 0 | False | True |
| E: erase tile coordinates | `before_ipl_from_retiled_old` | Definition | 2253-2257 | 5 | 0 | 17 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_point_source` | Definition | 2259-2271 | 13 | 0 | 4 | 0 | False | True |
| E: erase tile coordinates | `before_ipl_from_retiled_old_source` | Definition | 2273-2277 | 5 | 0 | 0 | 0 | False | False |
| E: erase tile coordinates | `before_of_retiled_old_point_eq_source_if_identity` | Lemma | 2279-2293 | 15 | 10 | 1 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_pprog_point` | Definition | 2295-2305 | 11 | 0 | 7 | 0 | False | True |
| E: erase tile coordinates | `before_ipl_from_retiled_old_pprog` | Definition | 2307-2312 | 6 | 0 | 4 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_pprog_point_source` | Definition | 2314-2325 | 12 | 0 | 1 | 0 | False | False |
| E: erase tile coordinates | `before_ipl_from_retiled_old_pprog_source` | Definition | 2327-2332 | 6 | 0 | 0 | 0 | False | False |
| E: erase tile coordinates | `before_of_retiled_old_pprog_point_app_head` | Lemma | 2334-2348 | 15 | 7 | 2 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_pprog_point_app_tail` | Lemma | 2350-2370 | 21 | 13 | 0 | 0 | False | False |
| E: erase tile coordinates | `before_ipl_from_retiled_old_pprog_app` | Lemma | 2372-2385 | 14 | 6 | 2 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_key` | Definition | 2387-2388 | 2 | 0 | 8 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_ltb` | Definition | 2390-2393 | 4 | 0 | 10 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_eqb` | Definition | 2395-2398 | 4 | 0 | 12 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_ltb_trans` | Lemma | 2400-2410 | 11 | 9 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_eqb_trans` | Lemma | 2412-2422 | 11 | 9 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_eqb_refl` | Lemma | 2424-2431 | 8 | 6 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_eqb_symm` | Lemma | 2433-2440 | 8 | 6 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_cmp_total` | Lemma | 2442-2454 | 13 | 11 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_eqb_ltb_implies_ltb` | Lemma | 2456-2472 | 17 | 15 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_ltb_eqb_implies_ltb` | Lemma | 2474-2492 | 19 | 17 | 4 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_eqb_implies_np_eq` | Lemma | 2494-2511 | 18 | 14 | 1 | 0 | False | True |
| E: erase tile coordinates | `instr_point_np_ltb_implies_np_lt` | Lemma | 2513-2535 | 23 | 19 | 1 | 0 | False | True |
| E: erase tile coordinates | `sortedb_instr_point_np_implies_sorted_np` | Lemma | 2537-2572 | 36 | 31 | 4 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_point_prefix` | Lemma | 2574-2595 | 22 | 14 | 2 | 0 | False | True |
| E: erase tile coordinates | `before_index_of_retiled_old_length` | Lemma | 2597-2616 | 20 | 11 | 2 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_point_old_of_compose_tiling_instr_point_ext` | Lemma | 2618-2679 | 62 | 47 | 1 | 0 | False | False |
| E: erase tile coordinates | `tiled_added_part_length` | Lemma | 2681-2691 | 11 | 7 | 8 | 18 | True | True |
| E: erase tile coordinates | `tiled_point_part_length` | Lemma | 2693-2702 | 10 | 6 | 6 | 18 | True | True |
| E: erase tile coordinates | `tiled_index_split` | Lemma | 2704-2720 | 17 | 11 | 8 | 18 | True | True |
| E: erase tile coordinates | `tiling_rel_pprog_structure_compiled_before_of_retiled_old_point_belongs_to_nth` | Theorem | 2722-2838 | 117 | 88 | 1 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pprog_structure_source_before_of_retiled_old_point_belongs_to_nth` | Theorem | 2840-2980 | 141 | 112 | 1 | 0 | False | True |
| E: erase tile coordinates | `tiling_rel_pinstr_structure_source_before_of_retiled_old_point_injective` | Theorem | 2982-3238 | 257 | 223 | 1 | 0 | False | True |
| E: erase tile coordinates | `before_ipl_from_retiled_old_forward_source` | Lemma | 3240-3321 | 82 | 51 | 2 | 0 | False | True |
| E: erase tile coordinates | `tiling_rel_pinstr_structure_source_before_of_retiled_old_sched_le_iff` | Theorem | 3323-3518 | 196 | 167 | 1 | 0 | False | False |
| E: erase tile coordinates | `HdRel_before_of_retiled_old_preserved_source` | Lemma | 3520-3561 | 42 | 18 | 1 | 0 | False | False |
| E: erase tile coordinates | `before_of_retiled_old_sorted_sched_preserved_source` | Lemma | 3563-3594 | 32 | 12 | 0 | 0 | False | False |
| E: erase tile coordinates | `before_ipl_from_retiled_old_forward` | Lemma | 3596-3671 | 76 | 45 | 2 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_point_injective` | Theorem | 3673-3889 | 217 | 191 | 1 | 0 | False | False |
| E: erase tile coordinates | `before_ipl_from_retiled_old_nodup` | Lemma | 3891-3948 | 58 | 32 | 2 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_time_stamp` | Theorem | 3950-4041 | 92 | 78 | 1 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pinstr_structure_source_before_of_retiled_old_time_stamp` | Theorem | 4043-4138 | 96 | 79 | 1 | 0 | False | True |
| E: erase tile coordinates | `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_sched_le_iff` | Theorem | 4140-4187 | 48 | 26 | 1 | 0 | False | False |
| E: erase tile coordinates | `HdRel_before_of_retiled_old_preserved` | Lemma | 4189-4226 | 38 | 20 | 1 | 0 | False | False |
| E: erase tile coordinates | `before_of_retiled_old_sorted_sched_preserved` | Lemma | 4228-4258 | 31 | 15 | 0 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pprog_structure_source_before_of_retiled_old_instr_semantics_iff_nth` | Theorem | 4260-4454 | 195 | 164 | 1 | 0 | False | True |
| E: erase tile coordinates | `before_of_retiled_old_list_semantics_preserved` | Lemma | 4456-4482 | 27 | 16 | 0 | 0 | False | False |
| E: erase tile coordinates | `instr_point_list_semantics_map_preserved` | Lemma | 4484-4507 | 24 | 16 | 1 | 0 | False | True |
| E: erase tile coordinates | `HdRel_sched_map_time_stamp_preserved` | Lemma | 4509-4527 | 19 | 12 | 1 | 0 | False | True |
| E: erase tile coordinates | `sorted_sched_map_time_stamp_preserved` | Lemma | 4529-4553 | 25 | 18 | 1 | 0 | False | True |
| E: erase tile coordinates | `tiling_rel_pprog_structure_compiled_old_point_belongs_to_nth` | Theorem | 4555-4645 | 91 | 67 | 1 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pprog_structure_compiled_before_point_has_retiled_old_preimage_nth` | Theorem | 4647-4746 | 100 | 64 | 1 | 0 | False | False |
| E: erase tile coordinates | `before_ipl_from_retiled_old_backward` | Lemma | 4748-4878 | 131 | 100 | 2 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pprog_structure_source_old_point_belongs_to_nth` | Theorem | 4880-4950 | 71 | 28 | 1 | 0 | False | True |
| E: erase tile coordinates | `tiling_rel_pprog_structure_source_before_point_has_retiled_old_preimage_nth` | Theorem | 4952-5089 | 138 | 103 | 1 | 0 | False | True |
| E: erase tile coordinates | `before_ipl_from_retiled_old_backward_source` | Lemma | 5091-5201 | 111 | 80 | 2 | 0 | False | True |
| E: erase tile coordinates | `flatten_instr_nth_implies_ip_nth` | Lemma | 5203-5215 | 13 | 8 | 2 | 0 | False | True |
| E: erase tile coordinates | `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists` | Theorem | 5217-5364 | 148 | 119 | 0 | 0 | False | False |
| E: erase tile coordinates | `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm` | Theorem | 5366-5534 | 169 | 140 | 1 | 0 | False | False |
| E: erase tile coordinates | `tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth` | Theorem | 5536-5622 | 87 | 61 | 0 | 0 | False | False |
| F: reconstruct intermediate lists | `retiled_old_of_after_point` | Definition | 5624-5639 | 16 | 0 | 8 | 0 | False | True |
| F: reconstruct intermediate lists | `after_point_of_retiled_old` | Definition | 5641-5651 | 11 | 0 | 6 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after` | Definition | 5653-5670 | 18 | 0 | 9 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_ipl_from_after` | Definition | 5672-5677 | 6 | 0 | 4 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_ipl_ext_from_after` | Definition | 5679-5684 | 6 | 0 | 7 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_pinstrs` | Fixpoint | 5686-5695 | 10 | 0 | 17 | 7 | True | True |
| F: reconstruct intermediate lists | `compose_tiling_pinstrs_ext_from_after` | Fixpoint | 5697-5706 | 10 | 0 | 8 | 108 | True | True |
| F: reconstruct intermediate lists | `retiled_old_of_after_point_preserves_np_fields` | Lemma | 5708-5714 | 7 | 3 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_preserves_np_fields` | Lemma | 5716-5726 | 11 | 3 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_of_after_point_belongs_to` | Lemma | 5728-5757 | 30 | 23 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `after_point_of_retiled_old_belongs_to` | Lemma | 5759-5788 | 30 | 23 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_belongs_to_ext` | Lemma | 5790-5835 | 46 | 37 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_new_of_ext` | Lemma | 5837-5847 | 11 | 6 | 2 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_old_of_ext` | Lemma | 5849-5860 | 12 | 7 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `after_matches_tiling_witness` | Definition | 5862-5866 | 5 | 0 | 6 | 39 | True | True |
| F: reconstruct intermediate lists | `retiled_old_of_after_point_after_inverse` | Lemma | 5868-5879 | 12 | 6 | 0 | 0 | False | False |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_after_inverse` | Lemma | 5881-5896 | 16 | 11 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `new_of_compose_tiling_ipl_ext_from_after` | Lemma | 5898-5911 | 14 | 9 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `old_of_compose_tiling_ipl_ext_from_after` | Lemma | 5913-5927 | 15 | 10 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_pinstr_eqdom_after` | Lemma | 5929-5940 | 12 | 8 | 1 | 0 | False | False |
| F: reconstruct intermediate lists | `tiling_rel_pinstr_list_compiled_witnesses` | Lemma | 5942-5962 | 21 | 14 | 1 | 0 | False | False |
| F: reconstruct intermediate lists | `retiled_old_pinstrs_eqdom_after_rel_list` | Lemma | 5964-5986 | 23 | 12 | 1 | 0 | False | False |
| F: reconstruct intermediate lists | `tiling_rel_pprog_structure_compiled_retiled_old_eqdom` | Lemma | 5988-6058 | 71 | 60 | 0 | 0 | False | False |
| F: reconstruct intermediate lists | `after_point_of_retiled_old_after_inverse` | Lemma | 6060-6074 | 15 | 10 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_of_after_point_injective_on_after_points` | Lemma | 6076-6089 | 14 | 7 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_of_after_point_of_retiled_old` | Lemma | 6091-6105 | 15 | 10 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `retiled_old_ipl_from_after_nodup` | Lemma | 6107-6137 | 31 | 26 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_injective` | Lemma | 6139-6149 | 11 | 6 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_ipl_ext_from_after_nodup` | Lemma | 6151-6174 | 24 | 20 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_instr_point_ext_from_after_preserves_np_lt` | Lemma | 6176-6191 | 16 | 10 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_ipl_ext_from_after_hdrel` | Lemma | 6193-6208 | 16 | 9 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_ipl_ext_from_after_sorted` | Lemma | 6210-6225 | 16 | 10 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `flatten_instr_nth_after_implies_flatten_instr_nth_retiled_old` | Theorem | 6227-6297 | 71 | 63 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `flatten_instr_nth_after_implies_flatten_instr_nth_tiling_ext` | Theorem | 6299-6388 | 90 | 82 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `nth_error_retiled_old_pinstrs` | Lemma | 6390-6409 | 20 | 12 | 2 | 0 | False | True |
| F: reconstruct intermediate lists | `nth_error_compose_tiling_pinstrs_ext_from_after` | Lemma | 6411-6430 | 20 | 12 | 0 | 13 | True | True |
| F: reconstruct intermediate lists | `retiled_old_pinstrs_preserve_length` | Lemma | 6432-6446 | 15 | 9 | 5 | 1 | True | True |
| F: reconstruct intermediate lists | `compose_tiling_pinstrs_ext_from_after_preserve_length` | Lemma | 6448-6463 | 16 | 9 | 1 | 3 | True | True |
| F: reconstruct intermediate lists | `retiled_old_pinstrs_app_singleton` | Lemma | 6465-6484 | 20 | 9 | 3 | 0 | False | True |
| F: reconstruct intermediate lists | `compose_tiling_pinstrs_ext_from_after_app_singleton` | Lemma | 6486-6505 | 20 | 9 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `flatten_instrs_after_implies_tiling_ext_exists` | Theorem | 6507-6691 | 185 | 167 | 1 | 0 | False | True |
| F: reconstruct intermediate lists | `flatten_instrs_retiled_old_implies_before_exists_perm` | Theorem | 6693-6933 | 241 | 212 | 0 | 0 | False | False |
| G: semantic composition | `tiling_after_to_retiled_old_poly_correct` | Theorem | 6935-7056 | 122 | 97 | 1 | 0 | False | True |
| G: semantic composition | `flatten_instrs_retiled_old_member_nth_data` | Lemma | 7058-7198 | 141 | 105 | 0 | 0 | False | False |
| G: semantic composition | `before_ipl_from_retiled_old_nodup_source` | Lemma | 7200-7261 | 62 | 36 | 2 | 0 | False | True |
| G: semantic composition | `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_source` | Theorem | 7263-7410 | 148 | 119 | 0 | 0 | False | False |
| G: semantic composition | `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm_source` | Theorem | 7412-7580 | 169 | 140 | 1 | 0 | False | True |
| G: semantic composition | `flatten_instrs_retiled_old_member_nth_data_source` | Lemma | 7582-7724 | 143 | 107 | 2 | 0 | False | True |
| G: semantic composition | `flatten_instrs_retiled_old_member_instr_semantics_iff_source` | Theorem | 7726-7783 | 58 | 27 | 1 | 0 | False | True |
| G: semantic composition | `flatten_instrs_retiled_old_member_time_stamp_preserved_source` | Theorem | 7785-7852 | 68 | 42 | 1 | 0 | False | True |
| G: semantic composition | `flatten_instrs_retiled_old_implies_before_exists_perm_source` | Theorem | 7854-8108 | 255 | 228 | 1 | 0 | False | True |
| G: semantic composition | `tiling_retiled_old_to_before_poly_correct_with_env_len_source` | Theorem | 8110-8207 | 98 | 68 | 1 | 5 | True | True |
| G: semantic composition | `tiling_retiled_old_to_before_instance_correct_source` | Theorem | 8209-8277 | 69 | 42 | 0 | 2 | True | True |
| G: semantic composition | `tiling_retiled_old_to_before_poly_layer` | Definition | 8279-8296 | 18 | 0 | 2 | 5 | True | True |
| G: semantic composition | `tiling_after_to_before_poly_correct_via_retiled_old` | Theorem | 8298-8339 | 42 | 16 | 1 | 5 | True | True |
| G: semantic composition | `tiling_after_to_before_instance_correct_via_retiled_old` | Theorem | 8341-8389 | 49 | 24 | 0 | 0 | False | False |

## Exported declarations outside current qualified-use closure

These 62 declarations are not reached from any current qualified external use.  This does **not** prove that they are safe to remove: the repository may intentionally expose them as API, and unqualified uses introduced by future `Import` commands are not represented.  It does identify where compatibility wrappers or a legacy submodule would have no current internal cost.

- `source_view_of_tiled_pinstr` (290-303; internal callers 2)
- `source_view_of_tiled_pinstrs` (305-314; internal callers 2)
- `source_view_of_tiled_pprog` (370-380; internal callers 0)
- `compose_tiling_instr_point_ext` (426-449; internal callers 7)
- `tiling_rel_pinstr_list_lengths` (456-470; internal callers 3)
- `tiling_rel_pprog_structure_compiled_lengths` (488-509; internal callers 2)
- `tiling_rel_pinstr_list_app_singleton_inv` (528-570; internal callers 1)
- `tiling_rel_pprog_structure_compiled_app_singleton_inv` (616-647; internal callers 1)
- `lift_access_after_env_exact_cell` (742-753; internal callers 2)
- `tiling_rel_pinstr_structure_domain_decompose` (1369-1384; internal callers 0)
- `tiling_rel_pinstr_structure_domain_lifted_compiled` (1386-1435; internal callers 1)
- `tiling_rel_pinstr_structure_compiled_domain_lifted` (1437-1461; internal callers 4)
- `tiling_rel_pinstr_structure_compiled_domain_complete` (1527-1564; internal callers 4)
- `tiling_rel_pinstr_structure_compiled_index_complete` (1614-1640; internal callers 0)
- `tiling_rel_pinstr_structure_compiled_domain_iff` (1642-1668; internal callers 1)
- `tiling_rel_pinstr_list_compiled_nth` (1670-1691; internal callers 1)
- `tiling_rel_pprog_structure_compiled_nth` (1715-1738; internal callers 11)
- `tiling_rel_pprog_structure_compiled_domain_iff_nth` (1763-1801; internal callers 0)
- `tiling_rel_pinstr_structure_waccess_exact_cells` (1803-1822; internal callers 1)
- `tiling_rel_pinstr_structure_raccess_exact_cells` (1824-1843; internal callers 1)
- `tiling_rel_pinstr_structure_source_of_tiled` (1845-1857; internal callers 0)
- `tiling_rel_pinstr_structure_waccess_lifted` (1960-1981; internal callers 1)
- `tiling_rel_pinstr_structure_raccess_lifted` (1983-2004; internal callers 1)
- `tiling_rel_pinstr_structure_compiled_waccess_lifted` (2006-2023; internal callers 1)
- `tiling_rel_pinstr_structure_compiled_raccess_lifted` (2025-2042; internal callers 1)
- `tiling_rel_pprog_structure_compiled_waccess_lifted_nth` (2044-2081; internal callers 0)
- `tiling_rel_pprog_structure_compiled_raccess_lifted_nth` (2083-2119; internal callers 0)
- `tiling_rel_pinstr_structure_compiled_old_schedule_lifted` (2121-2141; internal callers 1)
- `tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth` (2143-2180; internal callers 0)
- `tiling_rel_pprog_structure_compiled_belongs_to_ext_nth` (2182-2225; internal callers 0)
- `before_ipl_from_retiled_old_source` (2273-2277; internal callers 0)
- `before_of_retiled_old_pprog_point_source` (2314-2325; internal callers 1)
- `before_ipl_from_retiled_old_pprog_source` (2327-2332; internal callers 0)
- `before_of_retiled_old_pprog_point_app_tail` (2350-2370; internal callers 0)
- `before_of_retiled_old_point_old_of_compose_tiling_instr_point_ext` (2618-2679; internal callers 1)
- `tiling_rel_pprog_structure_compiled_before_of_retiled_old_point_belongs_to_nth` (2722-2838; internal callers 1)
- `tiling_rel_pinstr_structure_source_before_of_retiled_old_sched_le_iff` (3323-3518; internal callers 1)
- `HdRel_before_of_retiled_old_preserved_source` (3520-3561; internal callers 1)
- `before_of_retiled_old_sorted_sched_preserved_source` (3563-3594; internal callers 0)
- `before_ipl_from_retiled_old_forward` (3596-3671; internal callers 2)
- `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_point_injective` (3673-3889; internal callers 1)
- `before_ipl_from_retiled_old_nodup` (3891-3948; internal callers 2)
- `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_time_stamp` (3950-4041; internal callers 1)
- `tiling_rel_pinstr_structure_compiled_before_of_retiled_old_sched_le_iff` (4140-4187; internal callers 1)
- `HdRel_before_of_retiled_old_preserved` (4189-4226; internal callers 1)
- `before_of_retiled_old_sorted_sched_preserved` (4228-4258; internal callers 0)
- `before_of_retiled_old_list_semantics_preserved` (4456-4482; internal callers 0)
- `tiling_rel_pprog_structure_compiled_old_point_belongs_to_nth` (4555-4645; internal callers 1)
- `tiling_rel_pprog_structure_compiled_before_point_has_retiled_old_preimage_nth` (4647-4746; internal callers 1)
- `before_ipl_from_retiled_old_backward` (4748-4878; internal callers 2)
- `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists` (5217-5364; internal callers 0)
- `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm` (5366-5534; internal callers 1)
- `tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth` (5536-5622; internal callers 0)
- `retiled_old_of_after_point_after_inverse` (5868-5879; internal callers 0)
- `retiled_old_pinstr_eqdom_after` (5929-5940; internal callers 1)
- `tiling_rel_pinstr_list_compiled_witnesses` (5942-5962; internal callers 1)
- `retiled_old_pinstrs_eqdom_after_rel_list` (5964-5986; internal callers 1)
- `tiling_rel_pprog_structure_compiled_retiled_old_eqdom` (5988-6058; internal callers 0)
- `flatten_instrs_retiled_old_implies_before_exists_perm` (6693-6933; internal callers 0)
- `flatten_instrs_retiled_old_member_nth_data` (7058-7198; internal callers 0)
- `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_source` (7263-7410; internal callers 0)
- `tiling_after_to_before_instance_correct_via_retiled_old` (8341-8389; internal callers 0)

## No current caller at all

These declarations have neither an internal caller nor a qualified external site.  They are the strongest dead-export candidates, still subject to the API caveat above.

- `source_view_of_tiled_pprog` (370-380)
- `tiling_rel_pinstr_structure_domain_decompose` (1369-1384)
- `tiling_rel_pinstr_structure_compiled_index_complete` (1614-1640)
- `tiling_rel_pprog_structure_compiled_domain_iff_nth` (1763-1801)
- `tiling_rel_pinstr_structure_source_of_tiled` (1845-1857)
- `tiling_rel_pprog_structure_compiled_waccess_lifted_nth` (2044-2081)
- `tiling_rel_pprog_structure_compiled_raccess_lifted_nth` (2083-2119)
- `tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth` (2143-2180)
- `tiling_rel_pprog_structure_compiled_belongs_to_ext_nth` (2182-2225)
- `before_ipl_from_retiled_old_source` (2273-2277)
- `before_ipl_from_retiled_old_pprog_source` (2327-2332)
- `before_of_retiled_old_pprog_point_app_tail` (2350-2370)
- `before_of_retiled_old_sorted_sched_preserved_source` (3563-3594)
- `before_of_retiled_old_sorted_sched_preserved` (4228-4258)
- `before_of_retiled_old_list_semantics_preserved` (4456-4482)
- `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists` (5217-5364)
- `tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth` (5536-5622)
- `retiled_old_of_after_point_after_inverse` (5868-5879)
- `tiling_rel_pprog_structure_compiled_retiled_old_eqdom` (5988-6058)
- `flatten_instrs_retiled_old_implies_before_exists_perm` (6693-6933)
- `flatten_instrs_retiled_old_member_nth_data` (7058-7198)
- `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_source` (7263-7410)
- `tiling_after_to_before_instance_correct_via_retiled_old` (8341-8389)
