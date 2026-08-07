# PolyLang.v proofs with at least 30 proof-body lines

Every entry below was read against its statement and callers. “Owned” means
the mathematical fact belongs to PolyLang even if the proof should be factored.

| Line | Proof | Lines | Assessment | Recommended treatment |
|---:|---|---:|---|---|
| 1318 | `exact_listzzs_cols_current_transformation_for_witness` | 49 | Owned witness/current-view invariant | Keep; factor repeated witness-dimension arithmetic |
| 1652 | `poly_semantics_concat` | 71 | Unreachable legacy implicit-scan composition; parallels `poly_lex_concat` | Quarantine or derive from a common scan-union lemma |
| 2099 | `flatten_instr_nth_current_view_iff` | 47 | Owned, but four near-identical membership directions | Introduce a generic `belongs_to`-extensional flatten lemma |
| 2208 | `flatten_instrs_app_singleton` | 75 | Generic flatten skeleton, duplicated by ext version | Prove once in a private parameterized flatten section |
| 2305 | `flatten_instrs_app_singleton_inv` | 112 | Generic rank partition, duplicated by ext version | Share partition/app theorem; retain public wrapper |
| 2445 | `flatten_instrs_nil_sub_nil` | 49 | Public structural corollary | Reprove from generic app/inverse/nil facts |
| 2616 | `belongs_to_implies_NoDupA_np` | 34 | PolyLang point-identity invariant | Keep; isolate point reconstruction injectivity helper |
| 2674 | `eqdom_pinstr_implies_flatten_instr_nth_exists` | 97 | Manual construction later subsumed by canonical retiming proof | Move retiming theorem earlier; make this an existential wrapper |
| 2790 | `same_elem_lt_sorted_implies_same_list_pre` | 99 | Fully generic list/order theorem | Move to `ListExt`/sorted utility; keep PolyLang alias |
| 2903 | `eqdom_pinstr_implies_flatten_instr_nth_retime` | 86 | Canonical live eq-domain argument | Keep; factor retimed-point membership conversion |
| 3040 | `eqdom_pinstrs_implies_flatten_instrs_exists` | 37 | Owned program-level lifting | Keep; can reuse a generic `Forall2`/append lifting lemma |
| 3105 | `eqdom_pinstr_implies_flatten_same_np_set` | 58 | Unreachable predecessor route | Remove after compatibility decision |
| 3173 | `same_np_set_cons_inv` | 130 | Unreachable generic setoid-sorted-list machinery | Move only if independently useful; otherwise remove branch |
| 3314 | `same_np_set_sorted_NoDupA_nth` | 64 | Unreachable predecessor route | Remove with `same_np_set` branch |
| 3391 | `sorted_same_ipl_lt_impossible` | 55 | Unreachable predecessor route | Remove with `same_np_set` branch |
| 3564 | `eqdom_same_ipl_length_lt_impossible` | 68 | Unreachable cardinality argument superseded by retiming | Remove with old branch |
| 3758 | `eqdom_pinstrs_implies_flatten_instr_nth_rel` | 34 | Unreachable older relation theorem | Preserve name via wrapper over primed retiming theorem if required |
| 3837 | `flatten_instrs_current_view_iff` | 34 | Owned current-view lifting | Keep; simplify singleton extraction and use shared flatten lifting |
| 3901 | `instance_list_semantics_current_view_iff` | 79 | Owned semantic bridge; two directions are duplicated and one uses `lazymatch` to recover a dependent list | Factor a `poly_instance_list_semantics_current_view_iff` helper |
| 4164 | `wf_pinstr_tiling_current_view_affine` | 83 | Owned well-formedness bridge | Factor access-list column preservation; avoid duplicate write/read induction |
| 4608 | `flatten_instrs_ext_app_singleton` | 86 | Same generic proof as normal append | Instantiate shared flatten theorem |
| 4716 | `flatten_instrs_ext_app_singleton_inv` | 122 | Same generic proof as normal inverse; line 4826 unfolds `np_lt` instead of `np_lt_ext` | Instantiate shared theorem; fix the brittle typo |
| 5187 | `sorted_ge_implies_ext_sorted_ge` | 35 | Owned old/new schedule bridge | Factor generic reverse-lex boolean conversion |
| 5291 | `instr_point_ext_new_sched_leb_trans` | 39 | Generic comparator fact | Derive from one lexicographic `<=` combinator theorem |
| 5335 | `instr_point_ext_new_sched_geb_trans` | 39 | Mirror of previous theorem | Obtain by argument reversal/one generic theorem |
| 5710 | `select_helper_list_ext_implies_old_normal` | 32 | Generic map homomorphism for `select_helper` | Move parameterized theorem to `SelectionSort` |
| 5762 | `selsort_instance_list_ext_implies_old_normal` | 39 | Generic map homomorphism for `selsort` | Move parameterized theorem to `SelectionSort` |
| 5825 | `stable_permut_multi_skip` | 200 | Generic stable-permutation list theorem; adjacent-swap side conditions duplicated twice | Move to `StablePermut`; extract one swap-admissibility lemma |
| 6033 | `sorted_implies_ord_all` | 83 | Generic sorted-list prefix property | Move to sorted/selection utility |
| 6123 | `select_helper_stable_permut` | 232 | Largest proof; entirely generic selection-sort/stability reasoning | Move parameterized theorem to `SelectionSort`/`StablePermut` |
| 6430 | `selsort_stable_permut` | 38 | Generic algorithm theorem | Move with previous theorem; retain instantiated wrapper |
| 6493 | `stable_permut_step_ext_lists_are_equivalent` | 141 | PolyLang-owned semantic adjacent-swap argument; forward/backward halves duplicated | Define a symmetric semantic-equivalence predicate and one swap lemma |
| 6662 | `stable_permut'_ext_lists_are_equivalent` | 66 | PolyLang semantic closure; forward/backward composition duplicated | Use reflexive/symmetric/transitive semantic-equivalence lemmas and explicit state instantiation |
| 6897 | `poly_lex_concat` | 57 | Owned scan semantics; structure mirrors dead `poly_semantics_concat` | Share scanned-union side-condition helpers |
| 7204 | `insert_zeros_commute_after_env` | 53 | Unreachable generic vector/list identity | Move to `LinalgExt` if retained |
| 7408 | `poly_elim_schedule_semantics_preserve` | 105 | Core code-generation correctness theorem | Keep; split done/progress scan-compatibility facts into named helpers |
| 7531 | `poly_elim_schedule_semantics_env_preserve` | 76 | Core environment-specialized wrapper | Keep; isolate the OpenScop/polyhedron algebra block as a helper |

## Automation finding

`stable_permut'_ext_lists_are_equivalent` ends with:

```coq
Unshelve. exact Instr.State.dummy_state. exact Instr.State.dummy_state.
```

These states are not part of the mathematical argument; they discharge evars
left by broad `eapply`/`eauto`. Replace the relevant applications with explicit
state arguments or `refine`. This removes the only `dummy_state` use in the file
and makes the semantic composition auditable.
