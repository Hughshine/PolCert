# ISSRefinement read-only audit summary

- 1,145 lines, 69 public declarations, 34 proofs, and 3 proofs with spans >=30 lines.
- 35 direct qualified roots reach 64 declarations. Five exported declarations are repository-unreferenced; none is a long proof.
- The checker establishes declarative cut shape; the long proofs are on the semantics path and derive subset, cover, and disjointness.
- The central theory is soundly factored at the conceptual level: every point selects one sign vector, completeness supplies a child, and NoDup makes children disjoint.
- The main readability gap is repeated recovery through `map fst (filter ... (combine ...))`, especially twice in the 135-line disjointness proof. Package indexed child and domain/sign facts.
- Reuse existing `dot_product_opp_r`, `List.map_nth_error`, `Misc.nth_error_map_iff`, and `Misc.Forall2_length`; remove two goal-shape `repeat match goal` blocks; make the 43-line obligations theorem call its immediately preceding length lemma.
- Preserve all public name/types and leave the five repository-unreferenced utilities for a separate API decision.

---

# Read-only audit: src/ISSRefinement.v

## Scope and parsing

- 1,145 source lines; 69 declarations, of which 34 are proof-bearing. Exactly 3 proofs have inclusive `Proof`..`Qed` spans of at least 30 lines.
- The file contains one root functor, four module aliases, no nested declaration module, no Section, no Ltac declaration, no mutual `with`, and no admitted/aborted proof. All 69 declarations are public.
- Qualified external uses are restricted to module aliases instantiated directly from `ISSRefinement`; generic names such as `ident` are not counted merely because another module has a field with the same basename. Internal reachability is a conservative token graph and can over-approximate under local shadowing.

## Public reachability

- 35 declarations have direct qualified uses. Their dependency closure contains 64 of 69 declarations.
- `ISSBoolChecker.v` directly uses 18 roots and reaches 22 declarations. It establishes the declarative shape/cut predicates; it does not depend on the later cover/disjoint refinement proofs.
- `ISSCutSemantics.v` and `ISSSemantics.v` directly use 28 roots and reach 62 declarations. All three long proofs are on this semantics path.
- `ISSValidator.v` re-exports four specification roots: `domain_partition_shape`, `domain_partition_shape_with_witness`, `domain_partition_cut_shape`, and `domain_partition_complete_cut_shape`.
- Five exported declarations are repository-unreferenced: `ident`, `payload_eq_except_domain_refl`, `all_iss_sign_vectors_length`, `domains_pairwise_disjoint_singleton`, and `stmt_partition_refinement_singleton`. The payload reflexivity lemma and the two singleton lemmas form one disconnected convenience branch; `ident` and the sign-vector length lemma are isolated. Treat all five as compatibility API, not deletion candidates during readability cleanup.

## Formal responsibility and core argument

1. A child preserves every source statement field except its domain, and its domain is the source domain conjoined with one signed constraint per affine cut.
2. `all_iss_sign_vectors n` enumerates all choices of negative/nonnegative sides for `n` cuts. Each point computes one satisfying vector via `iss_signs_for_point`.
3. Completeness ensures a child exists for that vector, proving coverage. The appended-domain construction proves every child is a subset of its parent.
4. A point cannot satisfy two distinct sign vectors. NoDup of child sign vectors therefore turns common membership into equal child indices, proving pairwise disjointness.
5. The final bridge assembles payload preservation, subset, cover, and disjointness into `domain_partition_refinement`, which the ISS semantics consumes.

The cover/disjoint arguments are the essential theory of this file. Boolean reflection belongs to `ISSBoolChecker`; execution semantics belongs to `ISSCutSemantics`/`ISSSemantics`; generic list and linear-algebra facts should live below this module.

## P0/P1 order

1. **P0.1 exact reuse:** replace `dot_product_opp_right_local`, `nth_error_map_some`, `nth_error_map_inv`, and `Forall2_length_eq` implementations with wrappers around `dot_product_opp_r`, `List.map_nth_error`, `Misc.nth_error_map_iff`, and `Misc.Forall2_length`.
2. **P0.2 goal-shape cleanup:** rewrite the two `repeat match goal` blocks in `payload_eq_except_domainb_correct` as explicit boolean-conjunction conversion and field construction.
3. **P0.3 child fact package:** factor filtered child-pair inversion, Forall2 relation lookup, source/constraint recovery, and domain-to-sign satisfaction. Apply it to subset, cover, and especially the 135-line disjointness proof.
4. **P0.4 assembly reuse:** make `domain_partition_complete_cut_shape_obligations` call the immediately preceding length lemma and destruct cut evidence once.
5. **P1.1 utility sinking:** move `NoDup_nth_error_injective` and `Forall2_combine_inv` to `Misc` if their other copies/users are consolidated; retain exported wrappers here.
6. **P1.2 theory presentation:** keep `iss_piece_constraints_correct`, point-sign completeness/functionality, cover, and disjointness as explicit named lemmas; do not replace their core inductions with broad automation.
7. **P1.3 dead-route review:** leave the five repository-unreferenced names untouched unless a separate public-API decision permits removal or localization.

## Tactic and duplication audit

- The only goal-shape tactics are two `repeat match goal` blocks in `payload_eq_except_domainb_correct` (lines 72 and 76).
- The whole file has 12 `eauto` calls across 8 proofs, one `tauto`, no `auto`, `intuition`, `firstorder`, custom-depth `eauto`, or user Ltac. Proof search is not the source of the long scripts.
- Exact or near-exact low-level duplication exists for dot-product negation and map/Forall2 list lemmas. `in_poly_app_inv_local` is also a generic one-step consequence duplicated in `Extractor.v`; avoid importing that higher module and sink the fact only if a low-level shared location is desired.
- Subset, cover, and disjointness repeat the same child lookup path through `children_for_parent = map fst (filter ... (combine ...))`. This is the main local abstraction gap.

## All >=30-line proofs

### `stmt_domain_cut_relation_cover` (declaration 766; span 48, body 46)

- **Role:** Proves coverage for one source parent. For a source-domain point it computes the point's unique sign vector, uses sign-partition completeness to select a child with that vector, and proves membership using the child's appended cut constraints.
- **Why long:** The point-classification/completeness argument is genuine ISS theory. About half the body is repeated map/filter/combine recovery of the selected child and its `stmt_domain_matches_cuts` evidence.
- **Refactor:** Add `child_pair_for_parent_relation_inv`, returning parent equality and the relevant Forall2 relation for an `In` child pair. Add a child-domain constructor from source membership plus satisfied signs. Keep the sign-vector witness argument visible.
- **Risk/use:** `medium`; internal callers 1; direct qualified external uses 0; semantics-reachable `yes`; checker-reachable `no`. Preserve public name/type.

### `stmt_domain_cut_relation_disjoint` (declaration 822; span 135, body 133)

- **Role:** Proves pairwise disjointness. If a point belongs to children at indices `i` and `j`, each child's sign vector satisfies all cuts; functionality makes the sign vectors equal, and NoDup of child sign rows forces `i = j`, contradicting the premise.
- **Why long:** This is the central uniqueness proof. Its 135 lines contain two almost identical endpoint reconstructions: map nth inversion, filtered parent recovery, Forall2 relation lookup, source/constraint reconstruction, domain-to-sign satisfaction, and mapped sign-row nth facts.
- **Refactor:** P0: introduce `nth_error_child_for_parent_inv` and `child_domain_sign_facts` records/lemmas, then build facts for endpoint 1 and endpoint 2. Use Rocq `map_nth_error` for the final sign-row nth facts. Preserve the short functionality + NoDup contradiction as the visible theorem core.
- **Risk/use:** `medium`; internal callers 1; direct qualified external uses 0; semantics-reachable `yes`; checker-reachable `no`. Preserve public name/type.

### `domain_partition_complete_cut_shape_obligations` (declaration 982; span 43, body 41)

- **Role:** Packages cut-shape evidence into the three refinement obligations: shape, target/witness length agreement, and per-parent subset/cover/disjointness.
- **Why long:** The proof is mostly composition. It manually re-derives target/witness length from `Forall2` even though `domain_partition_shape_stmt_witnesses_length` is declared immediately before it, and repeatedly projects the domain relation out of `Hcut`.
- **Refactor:** Reuse `domain_partition_shape_stmt_witnesses_length`; destruct `Hcut` and `Hcomplete` into named components once; invoke the three parent theorems. Keep this as the public boundary between checked cut shape and semantic refinement.
- **Risk/use:** `low`; internal callers 1; direct qualified external uses 0; semantics-reachable `yes`; checker-reachable `no`. Preserve public name/type.

## Important sub-threshold proofs

- `iss_piece_constraints_correct` (29 lines) is the induction connecting signed cut satisfaction to appended polyhedral constraints. It is essential theory and already reasonably structured.
- `domain_partition_refinement_from_obligations` (29 lines) combines payload preservation with subset/cover/disjoint facts. It is the readable final assembly and should remain explicit.
- `stmt_domain_cut_relation_all_subset` (24 lines) shares child lookup boilerplate with both long parent proofs and should use the same fact package.
- `payload_eq_except_domainb_correct` (20 lines) is not long but is the file's only goal-shape-fragile proof.

## Interface rule

- Preserve every existing public name and type. When implementation moves to `Misc`/PolyBase, keep the original declaration as a qualified wrapper.
- New child fact packages should initially be Local or remain in this functor; they express ISS proof plumbing rather than a new public certificate format.
- Do not change the definitions of complete sign partitions, cut shapes, or refinement obligations during readability cleanup.
