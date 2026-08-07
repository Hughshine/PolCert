# Extractor.v Declaration Inventory

Baseline: commit `9162178` on branch `proof/readability-cleanup`, before the
declaration-level cleanup. This makes source locations and proof sizes stable
review evidence.

Proof span counts include the `Proof.` and closing line; proof body counts
exclude both. References are computed after removing nested comments and
strings.

## Preamble

| Line | Kind | Name | Proof body | Reachable | Internal callers | External | Class |
|---:|---|---|---:|---|---:|---:|---|
| 34 | Definition | `ident` | 0 | True | 16 | 0 | internal-live |
## Affine frontend checks

| Line | Kind | Name | Proof body | Reachable | Internal callers | External | Class |
|---:|---|---|---:|---|---:|---:|---|
| 55 | Fixpoint | `expr_to_aff` | 0 | True | 13 | 0 | internal-live |
| 79 | Fixpoint | `wf_affine_expr` | 0 | True | 5 | 0 | internal-live |
| 88 | Fixpoint | `wf_affine_expr_list` | 0 | True | 3 | 0 | internal-live |
| 94 | Fixpoint | `wf_affine_test` | 0 | True | 3 | 0 | internal-live |
| 102 | Fixpoint | `wf_scop_stmt` | 0 | True | 31 | 0 | internal-live |
| 111 | Fixpoint (mutual) | `wf_scop_stmts` | 0 | True | 7 | 0 | internal-live |
| 117 | Lemma | `andb_true_iff_local0` | 1 | True | 3 | 0 | internal-live |
| 123 | Lemma | `wf_scop_instr_inv` | 2 | False | 0 | 0 | zero-reference |
| 132 | Lemma | `wf_scop_seq_inv` | 2 | True | 3 | 0 | internal-live |
| 141 | Lemma | `wf_scop_loop_inv` | 7 | True | 2 | 0 | internal-live |
| 157 | Lemma | `wf_scop_guard_inv` | 4 | True | 4 | 0 | internal-live |
| 169 | Lemma | `wf_scop_stmts_cons_inv` | 4 | True | 3 | 0 | internal-live |
| 181 | Lemma | `expr_to_aff_correct` | 33 | True | 5 | 0 | internal-live |
| 255 | Fixpoint | `exprlist_to_aff` | 0 | True | 12 | 0 | internal-live |
| 271 | Lemma | `exprlist_to_aff_length` | 7 | False | 0 | 0 | zero-reference |
| 285 | Lemma | `exprlist_to_aff_rows_cols` | 8 | False | 0 | 0 | zero-reference |
| 300 | Lemma | `exprlist_to_aff_correct` | 16 | True | 2 | 0 | internal-live |
| 324 | Definition | `normalize_affine` | 0 | True | 3 | 0 | internal-live |
| 327 | Definition | `normalize_affine_list` | 0 | True | 25 | 0 | internal-live |
| 330 | Definition | `normalize_access` | 0 | True | 1 | 0 | internal-live |
| 333 | Definition | `normalize_access_list` | 0 | True | 6 | 0 | internal-live |
| 336 | Definition | `lift_affine` | 0 | True | 3 | 0 | internal-live |
| 339 | Definition | `lift_affine_list` | 0 | True | 20 | 0 | internal-live |
| 342 | Fixpoint | `lift_affine_list_n` | 0 | True | 15 | 0 | internal-live |
| 348 | Lemma | `lift_affine_list_app` | 4 | True | 1 | 0 | internal-live |
| 358 | Lemma | `lift_affine_list_n_app` | 5 | True | 2 | 0 | internal-live |
| 370 | Lemma | `lift_affine_list_n_succ` | 4 | True | 2 | 0 | internal-live |
| 381 | Lemma | `lift_affine_satisfies_constraint` | 6 | True | 1 | 0 | internal-live |
| 394 | Lemma | `lift_affine_list_satisfies_constraint` | 6 | True | 3 | 0 | internal-live |
| 407 | Lemma | `in_poly_lift_affine_list` | 3 | True | 1 | 0 | internal-live |
| 416 | Lemma | `in_poly_lift_affine_list_n_app` | 4 | True | 6 | 0 | internal-live |
| 427 | Lemma | `lift_affine_eval` | 4 | True | 1 | 0 | internal-live |
| 438 | Lemma | `lift_affine_list_affine_product` | 6 | True | 2 | 0 | internal-live |
| 451 | Lemma | `affine_product_lift_affine_list_n_app` | 5 | True | 6 | 0 | internal-live |
| 463 | Lemma | `dot_product_repeat_zero_left` | 6 | True | 3 | 0 | internal-live |
| 475 | Lemma | `affine_product_seq_row` | 4 | False | 1 | 0 | internal-live |
| 485 | Lemma | `affine_product_loop_row` | 5 | True | 1 | 0 | internal-live |
| 496 | Lemma | `affine_product_app` | 4 | True | 8 | 0 | internal-live |
| 506 | Lemma | `affine_product_sched_prefix_seq` | 5 | True | 2 | 0 | internal-live |
| 518 | Lemma | `affine_product_sched_prefix_loop` | 5 | True | 4 | 0 | internal-live |
| 530 | Lemma | `in_poly_lift_app_cons2_inv` | 15 | True | 1 | 0 | internal-live |
| 554 | Definition | `normalize_affine_rev` | 0 | True | 3 | 0 | internal-live |
| 557 | Definition | `normalize_affine_list_rev` | 0 | True | 36 | 0 | internal-live |
| 560 | Definition | `normalize_access_rev` | 0 | False | 1 | 0 | internal-live |
| 563 | Definition | `normalize_access_list_rev` | 0 | False | 0 | 0 | zero-reference |
| 566 | Lemma | `normalize_affine_satisfies_constraint` | 6 | True | 1 | 0 | internal-live |
| 580 | Lemma | `normalize_affine_list_satisfies_constraint` | 5 | True | 2 | 0 | internal-live |
| 593 | Lemma | `normalize_affine_eval` | 5 | False | 1 | 0 | internal-live |
| 606 | Lemma | `normalize_affine_list_affine_product` | 6 | False | 1 | 0 | internal-live |
| 619 | Lemma | `dot_product_rev` | 8 | True | 1 | 0 | internal-live |
| 634 | Lemma | `dot_product_env_rev_vec` | 8 | True | 2 | 0 | internal-live |
| 649 | Lemma | `normalize_affine_rev_eval` | 11 | True | 1 | 0 | internal-live |
| 668 | Lemma | `normalize_affine_list_rev_affine_product` | 6 | True | 10 | 0 | internal-live |
| 681 | Lemma | `normalize_affine_rev_satisfies_constraint` | 12 | True | 1 | 0 | internal-live |
| 701 | Lemma | `normalize_affine_list_rev_satisfies_constraint` | 5 | True | 4 | 0 | internal-live |
| 714 | Lemma | `exprlist_to_aff_normalized_correct` | 4 | False | 0 | 0 | zero-reference |
| 726 | Lemma | `exprlist_to_aff_rev_normalized_correct` | 5 | True | 4 | 0 | internal-live |
| 739 | Definition | `resolve_access_functions` | 0 | True | 7 | 0 | internal-live |
| 761 | Lemma | `resolve_access_functions_sound` | 17 | False | 0 | 0 | zero-reference |
| 785 | Definition | `make_le_constr` | 0 | True | 2 | 0 | internal-live |
| 800 | Definition | `make_ge_constr` | 0 | True | 2 | 0 | internal-live |
| 810 | Lemma | `dot_product_opp_right` | 2 | True | 3 | 0 | internal-live |
| 818 | Lemma | `make_le_constr_correct` | 6 | True | 2 | 0 | internal-live |
| 833 | Lemma | `make_ge_constr_correct` | 6 | True | 2 | 0 | internal-live |
| 848 | Lemma | `andb_true_r_local` | 1 | True | 2 | 0 | internal-live |
| 854 | Lemma | `andb_true_iff_local` | 1 | True | 16 | 0 | internal-live |
| 862 | Fixpoint | `test_to_aff` | 0 | True | 12 | 0 | internal-live |
| 885 | Lemma | `test_to_aff_sound` | 30 | True | 1 | 0 | internal-live |
| 923 | Lemma | `test_to_aff_complete` | 39 | True | 1 | 0 | internal-live |
| 970 | Lemma | `test_to_aff_sound_normalized` | 3 | True | 1 | 0 | internal-live |
| 982 | Lemma | `test_to_aff_complete_normalized` | 3 | True | 2 | 0 | internal-live |
| 994 | Lemma | `test_false_implies_not_in_poly_normalized` | 8 | True | 5 | 0 | internal-live |
| 1011 | Lemma | `guard_constraints_sound` | 4 | True | 1 | 0 | internal-live |
| 1026 | Lemma | `guard_constraints_complete` | 6 | False | 1 | 0 | internal-live |
| 1043 | Lemma | `guard_constraints_complete_in_poly` | 3 | False | 1 | 0 | internal-live |
| 1056 | Lemma | `guard_constraints_sound_in_poly` | 3 | True | 4 | 0 | internal-live |
| 1069 | Lemma | `wf_affine_expr_true_expr_to_aff_success` | 25 | False | 2 | 0 | internal-live |
| 1101 | Lemma | `wf_affine_expr_list_true_exprlist_to_aff_success` | 9 | False | 0 | 0 | zero-reference |
| 1117 | Lemma | `wf_affine_test_true_test_to_aff_success` | 14 | False | 0 | 0 | zero-reference |
| 1139 | Definition | `lb_to_constr` | 0 | True | 11 | 0 | internal-live |
| 1152 | Lemma | `lb_to_constr_sound` | 20 | True | 2 | 0 | internal-live |
| 1181 | Definition | `ub_to_constr` | 0 | True | 11 | 0 | internal-live |
| 1194 | Lemma | `ub_to_constr_sound` | 22 | True | 2 | 0 | internal-live |
| 1225 | Lemma | `loop_bounds_sound` | 3 | True | 2 | 0 | internal-live |
| 1239 | Lemma | `loop_constraints_complete` | 11 | False | 0 | 0 | zero-reference |
| 1261 | Lemma | `loop_constraints_complete_lifted` | 5 | True | 4 | 0 | internal-live |
| 1277 | Lemma | `loop_constraints_sound_lifted` | 15 | True | 2 | 0 | internal-live |
| 1303 | Lemma | `in_poly_app_inv` | 4 | False | 1 | 0 | internal-live |
| 1314 | Lemma | `in_poly_app_cons2_inv` | 9 | False | 0 | 0 | zero-reference |
| 1332 | Lemma | `in_poly_guard_split` | 5 | True | 4 | 0 | internal-live |
| 1345 | Lemma | `in_poly_normalize_affine_list_rev_app_inv` | 6 | True | 6 | 0 | internal-live |
| 1360 | Lemma | `firstn_length_decompose` | 9 | True | 10 | 0 | internal-live |
| 1378 | Lemma | `skipn_length_S_singleton` | 14 | True | 5 | 0 | internal-live |
| 1399 | Lemma | `dot_product_firstn_right` | 9 | False | 1 | 0 | internal-live |
| 1415 | Lemma | `dot_product_firstn_left` | 5 | False | 1 | 0 | internal-live |
| 1427 | Lemma | `satisfies_constraint_prefix` | 3 | False | 1 | 0 | internal-live |
| 1439 | Lemma | `in_poly_prefix` | 8 | False | 0 | 0 | zero-reference |
| 1456 | Lemma | `normalize_affine_list_rev_rows_cols` | 6 | False | 0 | 0 | zero-reference |
## Syntax-directed statement extraction

| Line | Kind | Name | Proof body | Reachable | Internal callers | External | Class |
|---:|---|---|---:|---|---:|---:|---|
| 1475 | Fixpoint | `extract_stmt` | 0 | True | 67 | 2 | confirmed-external |
| 1524 | Fixpoint (mutual) | `extract_stmts` | 0 | True | 22 | 0 | internal-live |
| 1546 | Lemma | `extract_stmt_instr_success_inv` | 9 | True | 6 | 0 | internal-live |
| 1576 | Lemma | `extract_stmt_seq_success_inv` | 2 | True | 6 | 0 | internal-live |
| 1585 | Lemma | `extract_stmt_loop_success_inv` | 7 | True | 11 | 0 | internal-live |
| 1603 | Lemma | `extract_stmt_guard_success_inv` | 6 | True | 12 | 0 | internal-live |
| 1620 | Lemma | `extract_stmts_cons_success_inv` | 11 | True | 6 | 0 | internal-live |
| 1642 | Lemma | `extract_stmts_nil_success_inv` | 2 | True | 8 | 0 | internal-live |
| 1651 | Definition | `lower_ip_depth` | 0 | False | 9 | 0 | internal-live |
| 1661 | Definition | `lower_pi_depth` | 0 | False | 2 | 0 | internal-live |
| 1680 | Lemma | `extract_stmt_lower_env_dim` | 104 | False | 1 | 0 | internal-live |
| 1685 | Lemma (mutual) | `extract_stmts_lower_env_dim` | 104 shared `extract_stmt_lower_env_dim` | False | 1 | 0 | internal-live |
| 1797 | Definition | `pi_has_lifted_prefix` | 0 | True | 1 | 0 | internal-live |
| 1807 | Definition | `pi_has_lifted_sched_prefix` | 0 | True | 1 | 0 | internal-live |
| 1817 | Lemma | `extract_stmt_has_lifted_prefix` | 58 | True | 8 | 0 | internal-live |
| 1822 | Lemma (mutual) | `extract_stmts_has_lifted_prefix` | 58 shared `extract_stmt_has_lifted_prefix` | True | 1 | 0 | internal-live |
| 1888 | Lemma | `extract_stmt_has_lifted_sched_prefix` | 60 | True | 7 | 0 | internal-live |
| 1893 | Lemma (mutual) | `extract_stmts_has_lifted_sched_prefix` | 60 shared `extract_stmt_has_lifted_sched_prefix` | True | 1 | 0 | internal-live |
| 1961 | Lemma | `extract_stmt_member_positive_depth` | 5 | False | 0 | 0 | zero-reference |
## Checked extractor entry point

| Line | Kind | Name | Proof body | Reachable | Internal callers | External | Class |
|---:|---|---|---:|---|---:|---:|---|
| 1980 | Definition | `check_extracted_wf` | 0 | True | 28 | 0 | internal-live |
| 1987 | Lemma | `check_extracted_wf_spec` | 5 | True | 3 | 1 | confirmed-external |
| 2000 | Lemma | `check_extracted_wf_app_inv` | 13 | False | 2 | 0 | internal-live |
| 2021 | Definition | `extractor` | 0 | True | 7 | 101 | confirmed-external |
| 2034 | Lemma | `extractor_success_implies_wf_scop` | 5 | True | 1 | 0 | internal-live |
| 2046 | Lemma | `extractor_success_implies_wf_check` | 8 | True | 1 | 1 | confirmed-external |
| 2062 | Lemma | `extractor_success_inv` | 9 | True | 2 | 0 | internal-live |
| 2081 | Lemma | `extractor_success_inv_full` | 5 | False | 0 | 0 | zero-reference |
| 2096 | Lemma | `extractor_success_implies_wf_pinstrs` | 13 | False | 0 | 0 | zero-reference |
| 2116 | Lemma | `extractor_success_implies_varctxt_le_vars` | 6 | True | 0 | 1 | confirmed-external |
| 2129 | Lemma | `flatten_instrs_singleton_inv` | 10 | False | 3 | 0 | internal-live |
| 2146 | Lemma | `flatten_instr_nth_in_inv` | 5 | False | 0 | 0 | zero-reference |
| 2161 | Lemma | `flatten_instr_nth_index_split` | 6 | False | 0 | 0 | zero-reference |
| 2177 | Lemma | `flatten_instrs_in_inv` | 9 | False | 0 | 0 | zero-reference |
| 2197 | Lemma | `flatten_instrs_in_intro` | 7 | True | 2 | 1 | confirmed-external |
| 2215 | Lemma | `flattened_point_satisfies_top_constraints` | 33 | False | 4 | 0 | internal-live |
| 2258 | Lemma | `flattened_point_loop_bounds` | 76 | False | 1 | 0 | internal-live |
| 2347 | Lemma | `flattened_point_loop_timestamp_head` | 80 | False | 1 | 0 | internal-live |
| 2442 | Lemma | `flattened_point_loop_index_prefix_bounds_and_timestamp_head` | 158 | False | 2 | 0 | internal-live |
| 2617 | Lemma | `loop_slice_point_fixed_prefix` | 55 | False | 2 | 0 | internal-live |
| 2695 | Lemma | `flattened_point_loop_fixed_prefix_implies_timestamp_head` | 31 | False | 1 | 0 | internal-live |
| 2740 | Lemma | `loop_slice_filter_iff_fixed_prefix` | 55 | False | 2 | 0 | internal-live |
| 2814 | Definition | `flatten_instrs_prefix_slice` | 0 | True | 24 | 0 | internal-live |
| 2829 | Lemma | `flatten_instrs_prefix_slice_nil` | 47 | True | 2 | 0 | internal-live |
| 2883 | Lemma | `flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice` | 169 | True | 3 | 0 | internal-live |
| 3071 | Lemma | `loop_slice_point_fixed_prefix_slice` | 37 | True | 1 | 0 | internal-live |
| 3137 | Lemma | `flattened_point_loop_fixed_prefix_implies_timestamp_head_slice` | 20 | True | 1 | 0 | internal-live |
| 3175 | Lemma | `loop_slice_filter_prefix_slice_gen` | 178 | True | 2 | 0 | internal-live |
| 3376 | Lemma | `flatten_instrs_prefix_slice_filter_left` | 46 | True | 2 | 0 | internal-live |
| 3431 | Lemma | `loop_slice_filter_prefix_slice` | 83 | False | 0 | 0 | zero-reference |
| 3532 | Lemma | `flattened_point_loop_bounds_and_timestamp_head` | 132 | False | 1 | 0 | internal-live |
| 3680 | Lemma | `flattened_point_schedule_has_top_prefix` | 32 | False | 2 | 0 | internal-live |
| 3724 | Lemma | `flattened_point_schedule_has_top_prefix_slice` | 48 | True | 1 | 0 | internal-live |
| 3788 | Lemma | `flattened_point_satisfies_top_constraints_slice` | 44 | True | 2 | 0 | internal-live |
| 3844 | Lemma | `flattened_guard_false_implies_nil_constrs_prefix` | 50 | False | 0 | 0 | zero-reference |
| 3907 | Lemma | `flattened_point_seq_pos_timestamp_with_prefix_slice` | 24 | True | 2 | 0 | internal-live |
| 3948 | Lemma | `flattened_point_seq_pos_timestamp` | 12 | False | 3 | 0 | internal-live |
| 3971 | Lemma | `lex_compare_cons_head_lt` | 6 | True | 3 | 0 | internal-live |
| 3984 | Lemma | `lex_compare_prefix_cons_head_lt` | 4 | True | 4 | 0 | internal-live |
| 3995 | Lemma | `instr_point_sched_le_from_cons_head_lt` | 5 | False | 1 | 0 | internal-live |
| 4009 | Lemma | `seq_pos_points_order` | 13 | False | 0 | 0 | zero-reference |
| 4036 | Lemma | `filter_all_false_nil` | 8 | True | 4 | 0 | internal-live |
| 4051 | Lemma | `filter_all_true_id` | 9 | True | 3 | 0 | internal-live |
| 4067 | Lemma | `filter_andb` | 6 | True | 1 | 0 | internal-live |
| 4079 | Lemma | `filter_negb_all_false_id` | 10 | True | 3 | 0 | internal-live |
| 4096 | Lemma | `sched_lt_not_sched_le_rev` | 9 | True | 1 | 0 | internal-live |
| 4112 | Lemma | `sorted_sched_head_le_all` | 3 | True | 1 | 0 | internal-live |
| 4123 | Lemma | `sorted_sched_filter_split_if_cross_lt` | 37 | True | 4 | 0 | internal-live |
| 4173 | Lemma | `sorted_filter_trans` | 23 | True | 1 | 0 | internal-live |
| 4204 | Lemma | `sorted_sched_filter` | 5 | True | 7 | 0 | internal-live |
| 4216 | Lemma | `nth_after_prefix_singleton` | 3 | True | 4 | 0 | internal-live |
| 4225 | Lemma | `sorted_sched_filter_split_by_prefix_head_bound` | 23 | True | 2 | 0 | internal-live |
| 4261 | Lemma | `sorted_sched_filter_split_by_prefix_head_eq` | 131 | True | 3 | 0 | internal-live |
| 4404 | Lemma | `sorted_sched_filter_ltb_succ_by_prefix_head` | 58 | True | 2 | 0 | internal-live |
| 4474 | Lemma | `flattened_guard_false_implies_nil` | 34 | False | 1 | 0 | internal-live |
| 4520 | Lemma | `flattened_guard_false_implies_nil_constrs` | 39 | False | 1 | 0 | internal-live |
| 4571 | Lemma | `flattened_guard_nonempty_implies_true` | 33 | False | 0 | 0 | zero-reference |
| 4615 | Lemma | `guard_false_core_case` | 18 | False | 0 | 0 | zero-reference |
| 4652 | Lemma | `guard_false_core_case_constrs` | 19 | False | 0 | 0 | zero-reference |
| 4690 | Lemma | `permutation_singleton` | 7 | True | 4 | 0 | internal-live |
| 4704 | Lemma | `instr_point_list_semantics_singleton_inv` | 5 | True | 4 | 0 | internal-live |
| 4718 | Lemma | `instr_point_list_semantics_nil_inv` | 2 | True | 4 | 0 | internal-live |
| 4727 | Lemma | `instr_point_list_semantics_app_inv` | 15 | True | 3 | 0 | internal-live |
| 4751 | Definition | `rebase_ip_nth` | 0 | True | 28 | 0 | internal-live |
| 4761 | Lemma | `lower_ip_depth_injective_pos` | 16 | False | 1 | 0 | internal-live |
| 4786 | Lemma | `np_lt_lower_ip_depth_iff` | 4 | False | 1 | 0 | internal-live |
| 4797 | Lemma | `instr_point_sema_lower_ip_depth` | 10 | False | 1 | 0 | internal-live |
| 4814 | Lemma | `instr_point_sched_le_lower_ip_depth` | 4 | False | 1 | 0 | internal-live |
| 4825 | Lemma | `rebase_ip_nth_injective_ge` | 12 | True | 1 | 0 | internal-live |
| 4846 | Lemma | `np_lt_rebase_ip_nth_iff` | 30 | True | 1 | 0 | internal-live |
| 4885 | Lemma | `instr_point_sema_rebase_ip_nth` | 10 | True | 1 | 0 | internal-live |
| 4902 | Lemma | `instr_point_sched_le_rebase_ip_nth` | 4 | True | 1 | 0 | internal-live |
| 4913 | Lemma | `sorted_sched_le_map_rebase_ip_nth` | 10 | True | 3 | 0 | internal-live |
| 4930 | Lemma | `sorted_sched_le_map_lower_ip_depth` | 10 | False | 0 | 0 | zero-reference |
| 4947 | Lemma | `instr_point_list_semantics_map_rebase_ip_nth` | 18 | True | 1 | 0 | internal-live |
| 4972 | Lemma | `instr_point_list_semantics_map_lower_ip_depth` | 18 | False | 0 | 0 | zero-reference |
| 4997 | Lemma | `belongs_to_lower_pi_depth` | 12 | False | 0 | 0 | zero-reference |
| 5018 | Lemma | `nodup_map_lower_ip_depth` | 20 | False | 0 | 0 | zero-reference |
| 5046 | Lemma | `sorted_np_lt_map_lower_ip_depth` | 10 | False | 0 | 0 | zero-reference |
| 5063 | Lemma | `instr_point_list_semantics_split_by_eq_app` | 4 | True | 3 | 0 | internal-live |
| 5077 | Lemma | `instr_point_list_semantics_split_by_eq_app_rebase_right` | 11 | True | 2 | 0 | internal-live |
| 5098 | Lemma | `flatten_instr_nth_all_nth` | 5 | False | 0 | 0 | zero-reference |
| 5111 | Lemma | `sorted_np_lt_map_rebase_ip_nth` | 17 | True | 3 | 0 | internal-live |
| 5136 | Lemma | `nodup_map_rebase_ip_nth` | 20 | True | 3 | 0 | internal-live |
| 5164 | Lemma | `flatten_instrs_prefix_slice_filter_right_rebase` | 134 | True | 2 | 0 | internal-live |
| 5309 | Lemma | `nth_error_map_inv` | 11 | False | 0 | 0 | bare-external-candidate |
| 5327 | Lemma | `flatten_instrs_loop_head_slice_prefix` | 118 | False | 0 | 0 | zero-reference |
| 5465 | Lemma | `flatten_instr_nth_map_rebase_ip_nth` | 63 | False | 0 | 0 | zero-reference |
| 5536 | Lemma | `flattened_stmts_pos_ge_with_prefix_slice` | 98 | True | 1 | 0 | internal-live |
| 5651 | Lemma | `seq_cons_cross_lt_by_nth_with_prefix_slice` | 21 | True | 1 | 0 | internal-live |
| 5689 | Lemma | `permutation_filter` | 12 | True | 3 | 0 | internal-live |
| 5708 | Lemma | `extract_stmts_cons_sorted_split_by_nth_prefix_slice` | 140 | True | 1 | 0 | internal-live |
| 5895 | Lemma | `extract_stmts_cons_semantics_split_by_nth_prefix_slice` | 42 | True | 1 | 0 | internal-live |
| 5975 | Lemma | `flatten_instrs_app_inv_rebase` | 181 | False | 1 | 0 | internal-live |
| 6168 | Lemma | `extract_stmts_cons_flatten_inv_rebase` | 26 | False | 3 | 0 | internal-live |
| 6212 | Lemma | `flattened_stmts_empty_prefix_pos_ge` | 52 | False | 1 | 0 | internal-live |
| 6276 | Lemma | `flattened_point_seq_pos_timestamp_with_prefix` | 16 | False | 2 | 0 | internal-live |
| 6305 | Lemma | `flattened_stmts_pos_ge_with_prefix` | 55 | False | 1 | 0 | internal-live |
| 6373 | Lemma | `seq_cons_cross_lt_by_nth` | 25 | False | 0 | 0 | zero-reference |
| 6414 | Lemma | `seq_cons_cross_lt_by_nth_with_prefix` | 30 | False | 1 | 0 | internal-live |
| 6460 | Lemma | `perm_partition_by_nth_threshold` | 49 | False | 1 | 0 | internal-live |
| 6522 | Lemma | `extract_stmts_cons_sorted_split_by_nth` | 101 | False | 1 | 0 | internal-live |
| 6650 | Lemma | `extract_stmts_cons_semantics_split_by_nth` | 43 | False | 2 | 0 | internal-live |
| 6725 | Lemma | `nodup_all_eq_singleton` | 14 | True | 3 | 0 | internal-live |
| 6748 | Lemma | `flatten_instr_nth_depth0_emptydom_singleton` | 52 | False | 1 | 0 | internal-live |
| 6816 | Lemma | `flatten_instr_nth_depth0_singleton_if_in_poly` | 51 | False | 2 | 0 | internal-live |
| 6883 | Lemma | `instance_list_semantics_inv` | 8 | True | 1 | 0 | internal-live |
| 6903 | Lemma | `poly_instance_list_semantics_inv` | 16 | True | 1 | 0 | internal-live |
| 6931 | Lemma | `loop_semantics_intro_from_envv` | 10 | True | 1 | 0 | internal-live |
| 6951 | Lemma | `loop_semantics_aux_implies_loop_semantics` | 13 | False | 1 | 0 | internal-live |
| 6971 | Lemma | `loop_instance_list_semantics_implies_loop_semantics` | 3 | False | 0 | 0 | zero-reference |
| 6981 | Lemma | `iter_semantics_app` | 9 | True | 2 | 0 | internal-live |
| 6999 | Lemma | `guard_true_semantics_with_eq` | 5 | False | 0 | 0 | zero-reference |
| 7015 | Lemma | `seq_cons_semantics_with_eq` | 5 | True | 3 | 0 | internal-live |
| 7031 | Lemma | `guard_branch_reduce` | 9 | False | 0 | 0 | zero-reference |
## Reconstruction of structured loop semantics

| Line | Kind | Name | Proof body | Reachable | Internal callers | External | Class |
|---:|---|---|---:|---|---:|---:|---|
| 7055 | Lemma | `instr_branch_core` | 35 | False | 0 | 0 | zero-reference |
| 7115 | Lemma | `instr_branch_core_with_constrs` | 44 | False | 0 | 0 | zero-reference |
| 7185 | Fixpoint | `stmt_size` | 0 | False | 2 | 0 | internal-live |
| 7192 | Fixpoint (mutual) | `stmt_list_size` | 0 | False | 1 | 0 | internal-live |
| 7198 | Lemma | `instr_branch_core_with_constrs_len` | 43 | False | 2 | 0 | internal-live |
| 7268 | Lemma | `flattened_guard_false_implies_nil_constrs_len` | 38 | False | 1 | 0 | internal-live |
| 7319 | Lemma | `guard_false_core_case_constrs_len` | 19 | False | 2 | 0 | internal-live |
| 7356 | Lemma | `flatten_instrs_prefix_slice_nil_implies_nil` | 8 | True | 1 | 0 | internal-live |
| 7371 | Lemma | `flatten_instr_prefix_slice_singleton_if_in_poly` | 60 | True | 1 | 0 | internal-live |
| 7447 | Lemma | `instr_branch_core_with_constrs_prefix_len` | 58 | True | 1 | 0 | internal-live |
| 7533 | Lemma | `iter_semantics_shift_start_with_state_eq` | 20 | True | 1 | 0 | internal-live |
| 7569 | Lemma | `iter_semantics_refine_with_state_eq` | 31 | True | 2 | 0 | internal-live |
| 7622 | Definition | `stmt_constrs_prefix_goal` | 0 | True | 1 | 0 | internal-live |
| 7637 | Definition | `stmts_constrs_prefix_goal` | 0 | True | 1 | 0 | internal-live |
| 7653 | Lemma | `core_sched_stmt_stmts_constrs_prefix_mutual` | 941 | True | 2 | 0 | internal-live |
## Derived compatibility entry points

| Line | Kind | Name | Proof body | Reachable | Internal callers | External | Class |
|---:|---|---|---:|---|---:|---:|---|
| 8609 | Lemma | `loop_slice_to_body_semantics_todo` | 113 | False | 1 | 0 | internal-live |
| 8755 | Lemma | `core_sched_loop_constrs_len_todo` | 573 | False | 3 | 0 | internal-live |
| 9349 | Definition | `stmt_constrs_goal` | 0 | False | 1 | 0 | internal-live |
| 9364 | Definition | `stmts_constrs_goal` | 0 | False | 1 | 0 | internal-live |
| 9379 | Lemma | `core_sched_stmt_stmts_constrs_mutual` | 212 | False | 1 | 0 | internal-live |
| 9597 | Lemma | `core_sched_seq_tail_constrs_len_todo` | 42 | False | 2 | 0 | internal-live |
| 9669 | Lemma | `extract_stmt_to_loop_semantics_core_sched_constrs_fuel` | 156 | False | 0 | 0 | zero-reference |
| 9843 | Lemma | `extract_stmt_to_loop_semantics_core_sched_constrs` | 16 | True | 3 | 0 | internal-live |
| 9876 | Lemma | `core_sched_loop_todo` | 7 | False | 0 | 0 | zero-reference |
| 9900 | Lemma | `core_sched_seq_head_todo` | 21 | False | 0 | 0 | zero-reference |
| 9948 | Lemma | `core_sched_seq_tail_todo` | 7 | False | 0 | 0 | zero-reference |
| 9985 | Lemma | `core_sched_guard_true_todo` | 31 | False | 0 | 0 | zero-reference |
| 10034 | Lemma | `extract_stmt_to_loop_semantics_core_sched` | 13 | True | 1 | 0 | internal-live |
| 10064 | Lemma | `extract_stmt_to_loop_semantics_core` | 2 | True | 1 | 0 | internal-live |
| 10089 | Theorem | `extractor_correct` | 26 | True | 0 | 10 | confirmed-external |
