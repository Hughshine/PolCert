# `src/ISSCutSemantics.v` declaration audit

## Scope and method

The inventory recognizes top-level `Definition`, `Fixpoint`, `Lemma`, and
`Theorem` declarations after removing nested comments and strings.  It records
source/proof spans, lexical dependencies, internal callers, qualified external
references (including discovered module aliases), and reachability from
repository-confirmed external roots.  Bare same-name matches are retained as
duplication evidence but are not counted as external calls.

Artifacts:

- `/tmp/polcert-isscutsemantics-declarations.csv`: machine-readable inventory
- `/tmp/polcert-isscutsemantics-declarations.md`: sectioned declaration table
- `/tmp/polcert-isscutsemantics-long-proofs.md`: all proofs with at least 30 body lines
- `/tmp/polcert-isscutsemantics-external-refs.txt`: qualified-root evidence and bare candidates
- `/tmp/polcert-isscutsemantics-rg-hits.txt`: raw repository search evidence

## Inventory

- 36 exported declarations: 30 lemmas, 3 definitions, 3 theorems.
- 866 unique proof-body lines.
- No local declarations, mutual blocks, inductives, records, or notations.
- One repository-confirmed external root:
  `iss_complete_cut_shape_to_before_correct`, called as
  `ISSSem.iss_complete_cut_shape_to_before_correct` at
  `src/ISSValidatorCorrect.v:27`.
- 35 declarations are transitively reachable from that root.
- One exact zero-reference declaration:
  `domain_partition_complete_cut_shape_nth_payload_relation` at line 480
  (12 proof-body lines).

All declarations are currently exported, so "no repository caller" is not a
license to remove a name.  Refactors should preserve the existing qualified
names and types unless compatibility is deliberately changed later.

## Proof architecture

The real theorem chain is compact:

1. A complete cut witness determines the unique child occurrence for every
   target instance (`complete_cut_shape_after_point_signs_match` and
   `before_of_after_point_injective_complete_cut_shape`).
2. Mapping all target instances back to their parents therefore preserves
   NoDup (`before_ipl_from_after_nodup_complete_cut_shape`).
3. Coverage supplied by `ISSRefinement` gives exactly the source instances;
   sorting the reconstructed points produces a legal source flattening
   (`flatten_instrs_after_implies_before_exists_perm_complete_cut_shape`).
4. Point execution and timestamps are preserved by `ISSSemantics`, so target
   polyhedral semantics imply source polyhedral semantics
   (`iss_complete_cut_shape_to_before_poly_correct`).
5. Equal variable contexts and variables lift that result to whole programs
   (`iss_complete_cut_shape_to_before_correct`).

This is a coherent backward-simulation proof.  The final three theorems are not
the main readability problem; their proof blocks correspond directly to the
semantic construction.

## Ownership findings

### Keep in `ISSCutSemantics`

- Complete-cut projections needed by the semantic proof.
- Canonical-sign agreement for a child-domain point.
- Injectivity/NoDup of the child-to-parent reconstruction.
- Flattening reconstruction and permutation.
- Polyhedral and whole-program correctness.

### Reuse from `TilingRelation` while preserving ISSCut names

`Module TileRel := TilingRelation Instr` is declared at line 27 but never used.
The following 17 declarations are copied or effectively copied from that exact
functor instance:

- `NoDup_map_on_local` (same as `TileRel.NoDup_map_on`).
- The complete comparator/order block from `instr_point_np_key` through
  `sortedb_instr_point_np_implies_sorted_np` (lines 71--258).
- `instr_point_list_semantics_map_preserved`,
  `HdRel_sched_map_time_stamp_preserved`, and
  `sorted_sched_map_time_stamp_preserved` (lines 260--329).

Because `PolIRs.PolyLang` and `TilingRelation Instr`'s `PL` are the same
`PolyLang Instr` instance, these are strong candidates for definition aliases
and one-line theorem wrappers.  This should be compile-tested before replacing
the current bodies, but it requires no public-name or theorem-type change.

`Forall2_nth_error_local` is also an exact local duplicate of
`TilingRelation.Forall2_nth_error`; `Misc.v` contains a related existential
variant.  Prefer a canonical shared/list implementation plus a compatibility
wrapper.

### Move conceptually to shared utilities

- `NoDup_map_value_unique`: generic `map`/NoDup fact.
- `NoDup_filter_nth_error_unique`: generic filtered-index uniqueness fact.
- `NoDup_np_eq_unique_implies_NoDupA`: generic bridge from Leibniz NoDup plus
  relation uniqueness to `NoDupA`.
- `lex_compare_eq_same_length_implies_eq_local`: generic lexicographic-list
  equality.  A second local copy exists as
  `lex_compare_eq_same_length_implies_eq_local_band` in
  `TilingBandScheduleValidator.v`.
- `belongs_to_same_source_same_np_implies_eq`: a `PolyLang` instance-point
  extensionality fact, not an ISS-cut fact.

The lowest-risk change is to introduce or reuse canonical lemmas in their
owning modules and keep the current ISSCut declarations as exact wrappers.

## Duplication, dead route, and intrinsic complexity

- The first 17 reusable declarations account for 208 proof-body lines and are
  already available in `TilingRelation`; they are accidental duplication, not
  ISS proof content.
- `domain_partition_complete_cut_shape_nth_payload_relation` is the only dead
  route.  It is a harmless projection lemma and may be retained as a
  compatibility wrapper; deleting it should be a last, explicit API decision.
- The 243-line injectivity theorem is the only substantially overgrown core
  proof.  Its central fact is genuinely nontrivial: disjoint complete cut
  pieces make child-to-parent reconstruction injective.  Its current size is
  not intrinsic.  `ISSRefinement.stmt_domain_cut_relation_disjoint` and
  `domain_partition_complete_cut_shape_obligations` already package the same
  partition-disjointness argument; a helper exposing unique child occurrence
  for a point can prevent a second low-level sign/filter proof here.
- The 95-line flattening theorem is intrinsically multi-stage and should remain
  explicit.  Its local sorting machinery can be reused, but compressing its
  semantic stages would hurt readability.
- The 57-line poly theorem and 39-line program theorem are proportionate glue
  and already provide a good top-down reading path.

## Remediation order with unchanged public API

### P0: remove clear duplication

1. Turn the comparator/order and mapped-semantics copies into wrappers around
   `TileRel` declarations.
2. Canonicalize `NoDup_map_on_local` and `Forall2_nth_error_local`; preserve
   their current names and types as wrappers.
3. Compile the file and all reverse dependencies with the project's normal
   `coqc` build/CI path after each group.

Expected result: roughly 200 proof-body lines disappear from the ISS-specific
file without changing the semantic proof or public symbols.

### P1: expose the semantic invariant

1. Add a private/member-witness helper for `flatten_instrs` membership.
2. Add a theorem, preferably in `ISSRefinement`, that two indexed children of
   one parent containing the same point are the same child occurrence under
   `domain_partition_complete_cut_shape`.  Derive it from the existing
   partition properties rather than repeating sign-vector plumbing.
3. Rewrite `before_of_after_point_injective_complete_cut_shape` as a composition
   of member lookup, reconstructed-field equality, unique child occurrence,
   and point extensionality.

Risk: medium.  The mathematical interface is already present, but connecting
global statement indices to the filtered per-parent child list requires careful
nth/filter bookkeeping.  Preserve the current theorem as a fallback until the
new helper compiles and its downstream proof is unchanged.

### P2: ownership cleanup

1. Canonicalize the generic NoDup/filter/lex facts in `ListExt` or another
   established utility module, retaining ISSCut wrappers.
2. Place the source-membership plus `np_eq` extensionality fact in `PolyLang`,
   retaining the existing ISSCut name as a wrapper.
3. Decide whether to retain the unused payload projection for downstream users;
   there is no current build reason to delete it.

Physical file splitting is not currently justified.  Once duplicated
infrastructure is removed and injectivity is factored, the remaining ~1,000
lines form one coherent semantic argument and compile dependencies would not
materially improve by splitting it.

## Reader route after cleanup

Read only these declarations in order:

1. `complete_cut_shape_after_point_signs_match`
2. `before_of_after_point_injective_complete_cut_shape`
3. `flatten_instrs_after_implies_before_exists_perm_complete_cut_shape`
4. `iss_complete_cut_shape_to_before_poly_correct`
5. `iss_complete_cut_shape_to_before_correct`

Everything else should read as a short projection, shared-library wrapper, or
private helper supporting that chain.

---

# ISSCutSemantics.v long-proof audit

Threshold: at least 30 proof-body lines.  Proof-body counts exclude `Proof.` and
the closing command.  The source snapshot is `proof/readability-cleanup` at the
time of the audit.

| Line | Declaration | Body lines | Ownership | Assessment | Recommended internal refactor |
|---:|---|---:|---|---|---|
| 389 | `NoDup_filter_nth_error_unique` | 40 | Generic list infrastructure | The statement says that a value which survives a filter cannot occur at two source indices when the filtered result is duplicate-free.  None of this is ISS-specific.  The induction repeats the same `filter_In` contradiction in the two asymmetric index cases. | Put one canonical lemma in `ListExt` (or reuse a standard/indexed NoDup lemma if available), and retain this public name as a one-line compatibility wrapper. |
| 504 | `complete_cut_shape_after_point_signs_match` | 36 | ISS cut semantics | This is a meaningful cut-specific fact: membership in the emitted child domain determines exactly the canonical sign vector for the point.  The proof follows the right mathematical path: obtain the per-statement cut relation, use the domain iff characterization, then use functional satisfaction of all cuts. | Keep the lemma and its proof idea.  Shorten the large positional invocation of `domain_partition_complete_cut_shape_nth_domain_relation` with a named projection/helper; do not hide the semantic argument behind automation. |
| 605 | `before_of_after_point_injective_complete_cut_shape` | 243 | Core ISS reconstruction | This is the central nontrivial result.  Equal reconstructed parents imply equal parent id, iteration vector, payload, and schedule data.  Complete/disjoint cut partitioning then forces the two child occurrences to be the same occurrence.  The mathematical obligation is essential, but the current proof is substantially inflated by destructing raw `InstrPoint` records at entry, reconstructing the same literals repeatedly, manually deriving both witness bounds, and interleaving sign uniqueness, filtered-child uniqueness, and record equality. | Factor three private lemmas: (1) a flatten-member witness lookup for an `InstrPoint`; (2) a complete-cut child-occurrence uniqueness theorem, preferably derived once from the already-proved `parent_partition_properties`/`domains_pairwise_disjoint` interface in `ISSRefinement`; (3) a small extensionality lemma for `before_of_after_point`/`set_ip_nth`.  Keep this theorem's public type and make its body a readable composition of those facts. |
| 1016 | `flatten_instrs_after_implies_before_exists_perm_complete_cut_shape` | 95 | Core flattening correspondence | The proof is long but well staged.  It reconstructs raw parent points, sorts them by `(statement,index)`, proves the exact flattening membership condition, proves NoDup/NoDupA, and concludes the required permutation.  This is the main reader-facing bridge from cut refinement to source instance realization. | Preserve the high-level blocks.  Replace the local comparator, SelectionSort laws, and `NoDup`/`NoDupA` bridge with canonical `TilingRelation` or shared list/order lemmas.  Add short local names for the reconstruction map and its permutation; avoid further tactic compression. |
| 1128 | `iss_complete_cut_shape_to_before_poly_correct` | 57 | Core polyhedral semantics | This is a clean semantic lift: invert the target instance-list semantics, reconstruct a source flattening, map the sorted execution back to parent points, preserve point semantics and timestamps, and rebuild the source derivation.  The proof witnesses the same final state and closes with state reflexivity. | Keep its structure.  Reuse the already existing `TilingRelation` map-semantics and sorted-timestamp lemmas through wrappers, eliminating duplicated proofs at lines 260--329. |
| 1206 | `iss_complete_cut_shape_to_before_correct` | 39 | Public whole-program glue | This is the only repository-confirmed external root.  It projects context/variable equality, inverts the target program semantics, calls the polyhedral theorem, and reconstructs the source program semantics.  Its length comes mainly from explicit constructor plumbing, not a missing mathematical abstraction. | Keep the public statement and a visible call to the polyhedral theorem.  A tiny private projection lemma for context/variable equality can reduce noise, but a cross-validator generic lifting abstraction is not justified unless several files use the same exact shape. |

## Detailed reading of the 243-line injectivity proof

The proof establishes the following chain.

1. `flatten_instrs` membership locates the two target points in target
   statements `after_pi1` and `after_pi2`.
2. Equality after `before_of_after_point` exposes equality of the parent
   statement ids and all point fields other than the target statement number.
3. The complete cut-shape relation associates each target statement with a
   source statement and a cut-sign witness.
4. Membership in each child domain makes both witnesses equal to the canonical
   sign vector of the common iteration point.
5. `parent_sign_partition_complete` makes equal signs identify a unique child
   pair.
6. NoDup of the filtered child-pair list turns equality of the child pair into
   equality of the original statement indices.
7. Equality of all record fields yields equality of the target points.

Steps 3--6 are the mathematical core.  Steps 1, 2, and 7 currently dominate
the syntax because record literals and nth-error arguments are expanded at
every use.  A reusable "unique child occurrence containing this source point"
lemma is the most valuable refactor.  `ISSRefinement.stmt_domain_cut_relation_disjoint`
already proves pairwise disjointness from exactly the same sign-functionality
and NoDup argument; the new helper should expose that established property
rather than reproduce its low-level proof in `ISSCutSemantics`.

## Automation and proof hygiene

- No `Admitted`, `admit`, `Abort`, `Unshelve`, `Axiom`, `Conjecture`, or
  `dummy_state` token occurs in this file.
- The file contains 35 `eauto` uses.  Most are local closing steps.  In the
  243-line proof, however, several large `eapply ...; eauto` calls obscure
  which completeness, nth-error, and membership facts discharge which
  premises.  The core helper lemmas should use explicit named arguments and
  hypotheses at the semantic boundary; routine list plumbing can remain
  automated.
- There is no evidence that broad automation is the source of a logical gap.
  The readability problem is theorem granularity and duplicated infrastructure,
  not unfinished proof search.
