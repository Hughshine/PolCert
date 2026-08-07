# Extractor Proof Audit

Baseline: commit `9162178` on branch `proof/readability-cleanup`.  This audit
uses the source before the cleanup described at the end of this document, so
line numbers and proof sizes remain stable.

## Scope and Method

The audit covers every declaration in `src/Extractor.v`, not only the final
correctness theorem.  It combines four checks:

1. Parse declarations, including names introduced by mutual `with` clauses,
   and associate each proof with its declarations.
2. Remove comments and strings, then build the exact-name dependency graph
   inside `Extractor.v`.
3. Search the repository for qualified uses through instantiated `Extractor`
   functors.  Bare same-name matches are not treated as API uses.
4. Read every proof of at least 30 lines and classify why it is long: genuine
   semantic argument, reusable library fact, special case of a stronger
   theorem, duplicated proof path, or presentation/automation overhead.

The complete 263-declaration table is in
[EXTRACTOR_DECLARATION_INVENTORY.md](EXTRACTOR_DECLARATION_INVENTORY.md).  It
records the baseline location, proof size, internal callers, observed external
uses, and reachability from the repository's public entry points.

## Quantitative Result

| Source region | Declarations | Unique proof-body lines | Public-root reachable |
|---|---:|---:|---:|
| Affine frontend | 98 | 590 | 75 |
| Syntax-directed extraction | 19 | 264 | 14 |
| Checks, flattening, and list reconstruction | 115 | 3,693 | 60 |
| Structural semantic reconstruction | 15 | 1,297 | 8 |
| Derived and historical entry points | 15 | 1,219 | 4 |
| Other preamble declaration | 1 | 0 | 1 |
| **Total** | **263** | **7,063** | **162** |

There are 101 declarations outside the dependency closure of the seven
observed repository entry points.  They contain 3,646 proof-body lines, or
51.6% of the file's proof text.  This does **not** by itself make them removable:
all are exported by the functor and may have out-of-tree users.  The safe
cleanup is to keep their names and statements while replacing duplicate proof
bodies with thin wrappers.

The seven observed repository entry points are:

| Declaration | Baseline line | Repository role |
|---|---:|---|
| `extract_stmt` | 1475 | Statement-level extraction used by LoopJam and tests |
| `check_extracted_wf_spec` | 1987 | Driver proof support |
| `extractor` | 2021 | Executable top-level extractor |
| `extractor_success_implies_wf_check` | 2046 | Driver proof support |
| `extractor_success_implies_varctxt_le_vars` | 2116 | Driver proof support |
| `flatten_instrs_in_intro` | 2197 | ISS/extractor bridge |
| `extractor_correct` | 10089 | Semantic correctness theorem |

## What Extractor Should Own

`Extractor.v` has one coherent responsibility: translate a structured affine
loop into a polyhedral program and prove that schedule-sorted extracted
instances reconstruct the original structured execution.  The declarations
that belong to that responsibility are:

- the executable affine-fragment checks and statement extractor;
- success inversion for each source constructor;
- extraction invariants for accumulated domains, schedules, depths, and
  statement numbers;
- the bridge from extracted polyhedral instructions to flattened instances;
- sequence partitioning by statement number and loop partitioning by the next
  iterator/timestamp coordinate;
- the structural statement/list reconstruction theorem;
- the top-level `extractor_correct` packaging theorem.

The central semantic route is:

```text
extractor_correct
  -> extract_stmt_to_loop_semantics_core
  -> extract_stmt_to_loop_semantics_core_sched
  -> extract_stmt_to_loop_semantics_core_sched_constrs
  -> core_sched_stmt_stmts_constrs_prefix_mutual
```

The last theorem is the real proof.  Its cases establish:

- **instruction:** the only flattened instance executes the source
  instruction with the same evaluated operands;
- **guard:** a true guard recurses into the body, while a false guard makes the
  extracted slice empty;
- **sequence:** statement-number ranges split the sorted instance list into a
  head execution and a rebased tail execution;
- **loop:** the next schedule coordinate partitions the list into consecutive
  iterator slices, each of which is reconstructed by the body induction
  hypothesis.

This structural induction is inherently substantial.  Its difficulty is the
conversion between a globally sorted flat list and syntax-directed execution,
not the affine conversion itself.

## What Should Move Elsewhere

Existing exported `Extractor.<name>` paths should remain as wrappers while the
canonical facts move to their natural owner.

| Destination | Declarations or families | Reason |
|---|---|---|
| `polygen/Loop.v` | `expr_to_aff`, `expr_to_aff_correct` | Already has byte-for-byte equivalent definitions and proof |
| `lib/Linalg.v` | `dot_product_repeat_zero_left`, `affine_product_app`, `dot_product_firstn_left/right`, generic affine-product prefix facts | These mention vectors/matrices, not extraction |
| `Misc.v` | `nth_error_map_inv` as a directional wrapper for `Misc.nth_error_map_iff` | The required map lookup equivalence already exists at this lower dependency layer |
| `ListExt.v` | `firstn_length_decompose`, `skipn_length_S_singleton`, filter-all facts, `filter_andb`, `permutation_filter`, and `nodup_all_eq_singleton` | These are generic structural and `NoDup` list facts; the owner audit confirms that adding them here is acyclic |
| `SortedListFacts.v` | `sorted_filter_trans` and generic sorted partition support | Generic `Sorting.Sorted` reasoning |
| `InstanceListSema.v` | nil/singleton/app semantic inversion, instance-list inversion | Same proofs are repeated in LoopJam and parallel codegen |
| `IterSemantics.v` | `iter_semantics_app`, start-state transport, elementwise refinement under `State.eq` | Generic iteration semantics |
| `polygen/Loop.v` | loop-semantics conversion and small guard/sequence composition facts | They mention only loop semantics and `State.eq` |
| Extractor instance layer | `lower_ip_depth`, `rebase_ip_nth`, their flattening and ordering facts | These encode statement-number repair caused by extraction/list concatenation |

`check_extracted_wf` currently imports the affine validator only to reuse its
poly-instruction well-formedness checker.  The underlying checker belongs in a
shared polyhedral well-formedness module, but that is a separate dependency
refactor rather than a proof-body cleanup.

## Exact Reuse Opportunities

The following are not merely similar proofs; their current statements can be
implemented by an existing theorem with at most a representation rewrite:

| Extractor declaration | Canonical fact |
|---|---|
| `expr_to_aff` | `Loop.expr_to_aff` |
| `expr_to_aff_correct` | `Loop.expr_to_aff_correct` |
| `andb_true_iff_local0`, `andb_true_iff_local` | `Bool.andb_true_iff` |
| `andb_true_r_local` | `Bool.andb_true_r` |
| `dot_product_repeat_zero_left` | `Linalg.dot_product_repeat_zero_left` |
| `permutation_singleton` | `Permutation_length_1_inv` |
| `nth_after_prefix_singleton` | `List.nth_middle` after normalizing singleton append |
| `nth_error_map_inv` | forward direction of `Misc.nth_error_map_iff` |
| `flatten_instrs_loop_head_slice_prefix` | `loop_slice_filter_prefix_slice` (identical statement) |

## Long-Proof Audit

Every baseline proof of at least 30 body lines is listed below.  “Keep” means
that the proof carries a real invariant or semantic argument; it may still be
factored into private helpers.  “Wrapper” means the public statement should
remain but its proof should delegate to a stronger theorem.

| Lines | Declaration | Why it is long | Decision |
|---:|---|---|---|
| 941 | `core_sched_stmt_stmts_constrs_prefix_mutual` | All four syntax cases and flat-list reconstruction meet here; loop case also contained unused local branches | Keep as the center; remove dead branches and factor constructor phases |
| 573 | `core_sched_loop_constrs_len_todo` | Repeats the loop case of the prefix mutual theorem at empty prefix | Wrapper |
| 212 | `core_sched_stmt_stmts_constrs_mutual` | A second mutual induction for the empty-prefix case | Wrapper for the two prefix projections |
| 181 | `flatten_instrs_app_inv_rebase` | Splits flattening across append and reconstructs rebased indices | Keep; later factor rebase round-trip and right-membership helpers |
| 178 | `loop_slice_filter_prefix_slice_gen` | General next-iterator slice equivalence; reverse direction repeats index arithmetic | Keep as master; factor the extended-prefix witness |
| 169 | `flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice` | Most general loop-slice invariant combines index, bounds, and timestamp | Keep as master |
| 158 | `flattened_point_loop_index_prefix_bounds_and_timestamp_head` | Non-slice predecessor of the general invariant | Reorder or derive from a shared core; do not retain two independent proofs |
| 156 | `extract_stmt_to_loop_semantics_core_sched_constrs_fuel` | Inducts on fuel although fuel does not occur in the conclusion | Wrapper; ignore the compatibility premise |
| 140 | `extract_stmts_cons_sorted_split_by_nth_prefix_slice` | Builds head/tail filters, permutations, and cross-order proof together | Keep; factor predicate names and sorted partition helper |
| 134 | `flatten_instrs_prefix_slice_filter_right_rebase` | Tail filter plus record reconstruction after statement-number rebasing | Keep; factor lower-bound and round-trip facts |
| 132 | `flattened_point_loop_bounds_and_timestamp_head` | Reproves two projections of the earlier joint theorem | Wrapper |
| 131 | `sorted_sched_filter_split_by_prefix_head_eq` | Three-way split of a sorted list by a timestamp coordinate | Keep; candidate for generic ordered-key partition helper |
| 118 | `flatten_instrs_loop_head_slice_prefix` | Identical statement to an earlier theorem | Wrapper |
| 113 | `loop_slice_to_body_semantics_todo` | Packages bounds, one-iteration slice, permutation, sortedness, and body IH | Keep as a compatibility bridge; factor the iteration package later |
| 104 | `extract_stmt_lower_env_dim` / `extract_stmts_lower_env_dim` | Mutual proof for an isolated historical transformation | Repository-unreachable; retain until API decision, then move beside depth lowering |
| 101 | `extract_stmts_cons_sorted_split_by_nth` | Empty-prefix predecessor of the prefix-slice partition family | Prefer wrapper/shared helper after declaration reordering |
| 98 | `flattened_stmts_pos_ge_with_prefix_slice` | Recovers tail membership across append and slice witnesses | Keep; factor left/right slice membership inversion |
| 83 | `loop_slice_filter_prefix_slice` | Empty-prefix predecessor proved independently of the general slice theorem | Wrapper after declaration reordering |
| 80 | `flattened_point_loop_timestamp_head` | Single projection proved separately | Wrapper after moving the joint master earlier |
| 76 | `flattened_point_loop_bounds` | Single projection proved separately | Wrapper after moving the joint master earlier |
| 63 | `flatten_instr_nth_map_rebase_ip_nth` | Rebuilds each instruction-point record after rebasing | Repository-unreferenced; retain as wrapper/helper candidate |
| 60 | `extract_stmt_has_lifted_sched_prefix` / `extract_stmts_has_lifted_sched_prefix` | Shared mutual proof of a genuine structural extraction invariant | Keep |
| 60 | `flatten_instr_prefix_slice_singleton_if_in_poly` | Most general singleton slice reconstruction | Keep as master |
| 58 | `extract_stmt_has_lifted_prefix` / `extract_stmts_has_lifted_prefix` | Shared mutual proof of a genuine structural extraction invariant | Keep |
| 58 | `sorted_sched_filter_ltb_succ_by_prefix_head` | Relates adjacent timestamp-prefix filters | Keep; reuse three-way partition infrastructure |
| 58 | `instr_branch_core_with_constrs_prefix_len` | General instruction semantic case at arbitrary prefix | Keep as master; make older depth-zero variants wrappers after reordering |
| 55 | `loop_slice_filter_iff_fixed_prefix` | Bidirectional membership characterization | Keep; reuse `nth_middle` |
| 55 | `loop_slice_point_fixed_prefix` | Derives fixed index and timestamp coordinates for one loop slice | Wrapper/helper candidate after the sliced joint invariant is moved earlier |
| 55 | `flattened_stmts_pos_ge_with_prefix` | Non-slice predecessor of tail-number lower bound | Shared membership helper/wrapper |
| 52 | `flattened_stmts_empty_prefix_pos_ge` | Further empty-prefix specialization | Wrapper |
| 52 | `flatten_instr_nth_depth0_emptydom_singleton` | Special singleton construction | Wrapper for the general singleton theorem after reordering |
| 51 | `flatten_instr_nth_depth0_singleton_if_in_poly` | Special singleton construction | Wrapper for the general singleton theorem after reordering |
| 50 | `flattened_guard_false_implies_nil_constrs_prefix` | General contradiction from false guard and slice membership | Keep as master |
| 49 | `perm_partition_by_nth_threshold` | Derives permutations for both filtered partitions | Keep or factor predicate-side helper |
| 48 | `flattened_point_schedule_has_top_prefix_slice` | Recovers schedule prefix from extraction and slice membership | Keep; share slice-index decomposition |
| 47 | `flatten_instrs_prefix_slice_nil` | Essential bridge between ordinary flattening and empty-prefix slicing | Keep |
| 46 | `flatten_instrs_prefix_slice_filter_left` | Characterizes the sequence-head filter | Keep; share left-membership inversion |
| 44 | `flattened_point_satisfies_top_constraints_slice` | Recovers accumulated constraints for a slice point | Keep; share slice-index decomposition |
| 44 | `instr_branch_core_with_constrs` | Depth-zero predecessor of the general instruction case | Wrapper after declaration reordering |
| 43 | `extract_stmts_cons_semantics_split_by_nth` | Packages a large sorted split into semantic endpoints | Keep as explicit packaging, then delegate partition facts |
| 43 | `instr_branch_core_with_constrs_len` | Depth-zero predecessor with explicit length | Wrapper after declaration reordering |
| 42 | `extract_stmts_cons_semantics_split_by_nth_prefix_slice` | Packages the prefix-slice split into semantic endpoints | Keep; statement size is intrinsic |
| 42 | `core_sched_seq_tail_constrs_len_todo` | Builds mapped tail permutation and sortedness before applying statement-list theorem | Keep as thin compatibility packaging |
| 39 | `test_to_aff_complete` | Structural Boolean/test conversion, mirrored by soundness | Keep; optionally share expression-pair evaluation helper |
| 39 | `flattened_guard_false_implies_nil_constrs` | Depth-zero guard contradiction with an initialization-derived environment length | Wrapper for the prefix master |
| 37 | `sorted_sched_filter_split_if_cross_lt` | Generic sorted/filter partition theorem | Move to sorted-list facts |
| 39 | `loop_slice_point_fixed_prefix_slice` | Fixed-prefix property with repeated `nth` arithmetic | Keep; reuse `nth_middle` |
| 38 | `flattened_guard_false_implies_nil_constrs_len` | Depth-zero copy of the prefix master | Wrapper |
| 37 | `instr_branch_core` | Empty-domain predecessor of the general instruction case | Wrapper after declaration reordering |
| 33 | `flattened_point_satisfies_top_constraints` | Empty-prefix predecessor of slice theorem | Wrapper after declaration reordering |
| 34 | `flattened_guard_false_implies_nil` | Empty-domain copy of the guard-false master | Wrapper |
| 33 | `flattened_guard_nonempty_implies_true` | Repeats the same guard contradiction | Boolean case split plus guard-false wrapper |
| 33 | `expr_to_aff_correct` | Duplicate of the loop language's affine-expression proof | Wrapper for `Loop.expr_to_aff_correct` |
| 32 | `flattened_point_schedule_has_top_prefix` | Empty-prefix predecessor of slice theorem | Wrapper after declaration reordering |
| 31 | `flattened_point_loop_fixed_prefix_implies_timestamp_head` | Combines the joint loop invariant with fixed-index evidence | Keep; reuse list-index fact |
| 31 | `iter_semantics_refine_with_state_eq` | Genuine elementwise refinement and state transport | Move to iteration semantics; use explicit inversion names |
| 30 | `test_to_aff_sound` | Structural Boolean/test conversion | Keep |
| 30 | `np_lt_rebase_ip_nth_iff` | Arithmetic proof that rebasing preserves statement order | Keep; current proof is robust for the pinned Rocq version |
| 30 | `seq_cons_cross_lt_by_nth_with_prefix` | Establishes strict cross-order for sequence partitions | Keep/share prefix-slice proof where possible |
| 30 | `core_sched_guard_true_todo` | Unpacks guard extraction and invokes the body theorem | Keep as compatibility wrapper; can share guard packaging |

## File Split

A readable split is possible without changing old functor paths:

```text
ExtractorFrontend.v   affine checks, conversion, and extract_stmt
ExtractorInstances.v  flattening, slices, ordering, and rebasing
ExtractorCorrect.v    structural reconstruction and extractor_correct
Extractor.v           compatibility facade using Include
```

The dependency is nearly linear, so this will not materially shorten a clean
build through parallelism.  It will improve reading and incremental rebuilds:
editing the final correctness proof will no longer recompile the first roughly
7,000 source lines.  The split should be a mechanical commit after proof-body
consolidation, not mixed with lemma movement.

## Cleanup Applied After the Baseline

The first cleanup keeps every existing declaration name and statement:

- aliases the duplicate expression conversion and proof to `Loop`;
- replaces exact standard/project-library duplicates with wrappers;
- replaces the duplicate loop-slice proof with a one-line theorem reuse;
- replaces the separate loop, mutual, and fuel proofs with empty-prefix
  specializations of the prefix mutual theorem;
- removes local assertions in the main loop case that had no downstream use;
- derives guard-false specializations from the prefix master;
- derives the combined loop bounds/timestamp theorem from the joint theorem;
- replaces goal-shape matching in iteration refinement with explicit names.

Cross-file lemma movement and the four-file split remain separate follow-up
changes because they affect dependency structure even when theorem statements
remain compatible.
