# `src/AffineValidator.v` proofs with at least 30 proof-body lines

All 23 entries were read against their statements, direct callers, and the
confirmed qualified external roots. "Essential" means the result belongs to
the validator's correctness chain; it does not mean the present proof shape is
irreducible.

| Line | Proof | Lines | Ownership and source of complexity | Recommended treatment |
|---:|---|---:|---|---|
| 748 | `check_wf_polyinstr_common_correct` | 120 | Essential Boolean-to-`wf_pinstr` reflection. Length follows the eleven sequential guards and two access-list traversals, not a difficult argument. | Keep local; factor named guard-extraction and access-column helpers so the proof mirrors the checker specification. |
| 1362 | `wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at` | 50 | Essential current-view pairing bridge. Positional destruction of nested conjunctions makes it brittle. | Keep here; use named projection lemmas for source/target well-formedness and one mapped-access column lemma. |
| 1760 | `ext_compose_same_length_app` | 33 | Generic `map2`/zip append fact for the obsolete non-`_at` pairing route. Repository-unreachable. | Put a generic zip/app lemma in `ListExt` only if needed; retain an exact wrapper for compatibility or remove with the old route. |
| 1843 | `ext_compose_app` | 40 | Obsolete non-current-view pairing composition. It depends only on the previous zip/app fact and projection maps. | Remove/quarantine with the non-`_at` route after external compatibility is decided. |
| 1896 | `eq_dom_pinstrs_implies_all_nil` | 62 | Obsolete proof that equivalent programs flatten to empty lists together. It reconstructs list suffixes with `last`/`removelast`. | Replace by a short consequence of the canonical retiming/flatten correspondence if the name must remain. |
| 1986 | `eqdom_pinstrs_implies_ext_compose` | 43 | Obsolete program-level non-`_at` paired-list route. | Keep only as a compatibility wrapper over the current-view construction, otherwise remove with its dependency cluster. |
| 2193 | `validate_two_accesses_helper_correct` | 77 | Essential enumeration of old-order/new-bad guard pairs, but it contains a second nested list induction. | Move `forallb_imp_true_forall` before this theorem and prove it like the 29-line integer counterpart. The iterator lemma is generic impure-list utility. |
| 2281 | `validate_two_accesses_implies_permut_no_collision` | 46 | Essential access-level collision kernel. The same proof reappears at line 5166 for the integer emptiness checker. | Factor a private theorem parameterized by the pair-checker soundness result; retain both public names and types. |
| 2546 | `no_write_collision_implies_permutable` | 126 | Core semantic theorem: absence of WW/WR/RW collisions permits swapping two instruction instances. Forward and backward halves repeat collision transposition. | Keep the PolyLang-facing theorem; extract one directional commutation lemma and generic transpose/symmetry facts. The instruction-only commutation premise belongs near `Instr`. |
| 2755 | `validated_access_checks_imply_no_write_collision` | 103 | Essential glue from three nested Boolean access checks to `no_write_collision`. Already a useful abstraction, but specialized to the rational checker. | Generalize privately over an access-pair checker and its soundness theorem, then instantiate for ordinary and integer checks. |
| 2943 | `validate_two_instrs_implies_no_write_collision` | 63 | Essential schedule-to-guard bridge. Most lines construct witnesses for `make_poly_lt` and `make_poly_ge`. | Keep; extract named old-order and new-bad guard-membership lemmas so this reads as a composition. |
| 3086 | `validate_pinstr_implies_permutability1` | 32 | Essential wrapper joining checked collisions to semantic permutability. Repeats point/program transformation equalities. | Keep; add a private lemma deriving `ip_access_transformation_ext = ip_transformation_ext` from flatten membership and ext well-formedness. |
| 3304 | `rel_pil_implies_rel_ipl` | 48 | Repository-unreachable predecessor route using normal flattenings and `eq_except_sched`. | Delete/quarantine after compatibility review; the live paired flatten theorem supersedes it. |
| 3382 | `validate_instr_and_list_implies_pointwise` | 63 | Essential and already appropriately generic over `P` and `R`. Complexity comes from the reverse traversal implemented by `validate_instr_and_list`. | Keep local. Small helpers for accepted head/tail results and `Forall` snoc inversion would improve names, but no major abstraction is needed. |
| 3670 | `expand_pinstr_implies_expand_pinstr_ext_at` | 252 | Core paired-instance theorem. It establishes all four `flatten_instr_nth_ext` clauses and synchronizes two normal lists by `eq_except_sched`; the result is substantive, but manual `nth_error` reconstruction inflates it. | Keep in the affine pairing layer. Factor forward membership, backward reconstruction, paired-list projections, and uniqueness-under-`eq_except_sched`; use a `Forall2`/zip API internally. |
| 3938 | `flatten_instrs_implies_flatten_instrs_ext_at` | 161 | Essential program-level lift of the previous theorem. `rev_ind` is natural for the existing flatten append API, but two inline inductions reprove paired-list lengths. | Reuse/move the existing `compose_pinstrs_ext_at_preserve_length` before this theorem and factor a snoc decomposition helper. |
| 4160 | `eqdom_pinstrs_implies_flatten_same_length` | 58 | Repository-unreachable old cardinality route. | If retained, derive it from per-instruction retiming length and a generic related-list fold; otherwise remove with the old route. |
| 4268 | `validate_pinstrs_ext_implies_permutability` | 58 | Essential exported kernel, also called three times by the direct band validator. Its four cases correspond to head/head, head/tail, tail/head, tail/tail. | Keep name/type and overall proof; only name the four membership cases and accepted-check projections. |
| 4397 | `validate_tiling_implies_permutability` | 105 | Essential top-level decomposition, but structurally duplicates the affine theorem at line 4704. | Establish one shared accepted-validator specification or prove affine acceptance refines general/tiling acceptance; keep this theorem as the canonical body. |
| 4523 | `permutable_instance_lists_preserve_semantics` | 74 | Semantic heart of the end-to-end result: lift the target permutation, stable-sort by old schedule, and invoke semantic stability. | Keep local and prominent. Factor only the permutation transport bookkeeping; do not hide the stable-sort argument behind automation. |
| 4704 | `validate_implies_permutability` | 109 | Affine-specialized duplicate of line 4397; differences are only the stronger affine well-formedness checker and its coercion to tiling/general well-formedness. | Make it a wrapper over a shared theorem or over `validate_tiling_implies_permutability` after proving checker refinement. |
| 5166 | `validate_two_accesses_integer_implies_permut_no_collision` | 46 | Live direct-band access kernel; nearly line-for-line duplicate of line 2281 except for integer pair soundness. | Instantiate the same private parameterized collision theorem as the ordinary checker. |
| 5280 | `validate_two_instrs_under_guards_integer_implies_no_write_collision` | 305 | Live, externally called direct-band theorem. Its three 60--70 line WW/WR/RW blocks repeat the abstraction already present at line 2755. The theorem is important; its present length is not intrinsic. | Highest-value refactor: instantiate a checker-parametric `validated_access_checks_imply_no_write_collision`; preserve this public name/type as a short wrapper. |

## Automation audit

The file contains no `Admitted`, `Abort`, `Unshelve`, or `dummy_state` proof
completion. Broad `eauto`, `firstorder`, `simpls`, and inversion tactics are
common, but the main readability problem is explicit structural duplication,
not hidden proof search. In the two core flattening proofs, replace broad
automation only after the membership/projection obligations are factored into
named lemmas; mechanically expanding every `eauto` first would make them less
readable.
