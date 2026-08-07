# `src/AffineValidator.v` declaration and ownership audit

Scope: `proof/readability-cleanup`, read-only. The inventory covers every
top-level proof/value declaration. This file contains no records, inductives,
notations, or mutual `with` declarations, so no generated projection,
constructor, alias, or mutual body had to be added. Nested comments and strings
are removed before dependency analysis.

Qualified external roots include direct functor instances and transitive module
aliases, notably `TilingValidator.TilingVal`, `BandAffine`, and
`Core.BandAffine`. There is no `Import`/`Export` of these aliases that would make
unqualified external calls ambiguous. Bare-name matches are retained separately
in the CSV and raw evidence rather than counted as confirmed API uses.

## Counts

| Conceptual section | Declarations | Unique proof-body lines | Confirmed external roots | Reachable | Unreachable proof lines |
|---|---:|---:|---:|---:|---:|
| Preamble | 1 | 0 | 1 | 1 | 0 |
| Executable validator and witness-aware routes | 48 | 131 | 13 | 44 | 13 |
| Boolean-check soundness | 13 | 252 | 6 | 13 | 0 |
| Paired-instance construction and projection | 45 | 554 | 0 | 20 | 356 |
| Pairwise dependence exclusion | 21 | 623 | 2 | 20 | 20 |
| Flattened-list lifting | 27 | 882 | 1 | 13 | 238 |
| End-to-end affine validation | 9 | 382 | 4 | 9 | 0 |
| Environment lifting and current-view bridge | 3 | 57 | 2 | 3 | 0 |
| Integer direct-band support | 9 | 414 | 2 | 9 | 0 |
| **Total** | **176** | **3,295** | **31** | **132** | **627** |

Kinds: 125 lemmas, 37 definitions, 10 fixpoints, and 4 theorems. Thirteen
lemmas are `Local`; the remaining 163 names are exported. There are 26 exact
zero-reference declarations. Repository reachability does not establish that
an exported name has no out-of-tree client.

## Public surface

| Name | Confirmed qualified external source hits | Role |
|---|---:|---|
| `check_valid_access` | 10 | Shared access-function gate |
| `validate` | 8 | Affine validator entry point |
| `check_valid_access_correct` | 8 | Shared access-check soundness |
| `validate_instr_list` | 5 | Pairwise instruction validator used by affine and band paths |
| `validate_general` | 5 | Historical/general witness-aware entry point |
| `check_wf_polyinstr` | 4 | Extractor/validator well-formedness check |
| `validate_implies_permutability` | 4 | Affine pairwise semantic result |
| `no_write_collision_implies_permutable` | 3 | Collision-to-commutation kernel reused by band validation |
| `validate_pinstrs_ext_implies_permutability` | 3 | Paired-list kernel reused by band validation |
| `validate_two_instrs_under_guards_integer` | 3 | Direct-band integer guard checker |
| `validate_two_instrs_under_guards_integer_implies_no_write_collision` | 3 | Direct-band collision theorem |

The direct-band clients make the access-conflict and paired-list core a shared
validator service. It is not dead code merely because it is below the affine
entry point.

## Correct ownership

AffineValidator should continue to own:

- the executable well-formedness, domain-equality, access-conflict, and affine
  validation pipelines and their Boolean soundness theorems;
- construction of the current-view paired instruction/list representation used
  to relate source and target flattened instances;
- the bridge from reversed old/new schedules to checked access noncollision and
  `PolyLang.Permutable_ext`;
- list-level lifting of pairwise permutability and the stable-sort argument that
  transports target execution back to source execution;
- the affine and witness-aware program-level correctness wrappers;
- the integer-feasibility access kernel exported to the direct permutable-band
  checker. It belongs in a shared validator kernel conceptually, but moving it
  out physically must preserve `AffineValidator.<name>` wrappers.

## Misowned or duplicated utility

1. **Point-witness equality is duplicated.** Lines 49--183 reproduce the six
   equality functions and six soundness lemmas already defined in
   `PointWitness.v` (the outer `point_space_witness_eqb` wrapper delegates its
   recursive cases back to `PointWitness`). Use aliases/thin wrappers with the
   existing AffineValidator names and types.
2. **Impure list iteration is generic.** `forallb_imp` and
   `forallb_imp_true_forall` are independent of affine scheduling. The latter
   should live beside the impure monad/list combinator. The unused head/tail
   lemmas can then be wrappers or removed.
3. **Zip/map2 structure is generic.** Equal-length zip append, membership,
   `nth_error`, projection-map, and length facts used by `compose_ipl_ext[_at]`
   should be provided by `ListExt`; the actual construction of paired
   instruction points remains validator-owned.
4. **Access-level semantic commutation is mostly instruction-generic.**
   `lift_access_noncollision_to_cells` and
   `no_w_collision_implies_permutability` only need instruction semantics and
   access-cell contracts. Their canonical versions belong near `Instr`; retain
   the PolyLang/ext-point wrapper here.
5. **Snoc/Forall decomposition is generic.** Several `rev_ind` proofs manually
   recover the final element of a related list and split `Forall` over
   `prefix ++ [last]`. Put named facts in `ListExt` rather than repeating
   `last`/`removelast` and inversion blocks.

## Canonical and obsolete routes

The live paired construction is the current-view `_at` family:

`compose_pinstr_ext_at` / `compose_pinstrs_ext_at` ->
`compose_ip_ext_at` / `compose_ipl_ext_at` ->
`expand_pinstr_implies_expand_pinstr_ext_at` ->
`flatten_instrs_implies_flatten_instrs_ext_at`.

The older non-`_at` pairing cluster contains 25 unreachable declarations and
356 proof-body lines. Its long members are `ext_compose_same_length_app`,
`ext_compose_app`, `eq_dom_pinstrs_implies_all_nil`, and
`eqdom_pinstrs_implies_ext_compose`. A second obsolete flatten/cardinality
cluster contributes 14 declarations and 238 proof lines. Do not delete either
cluster before deciding external compatibility; where a name matters, derive a
short wrapper from the current-view route.

The rational `validate_two_instrs_under_guards` route and its soundness theorem
are also repository-unreachable. The live band path intentionally uses
`validate_two_instrs_under_guards_integer`, which canonicalizes the final guard
intersection with `VplCanonizerZ` before asking VPL for emptiness.

One currently unreachable result should be promoted rather than removed:
`compose_pinstrs_ext_at_preserve_length` is proved at line 4247, while the live
161-line program lifting theorem proves its content twice inline at lines
4019--4029 and 4067--4074.

## Essential versus accidental complexity

- `expand_pinstr_implies_expand_pinstr_ext_at` (252 lines) is the main genuine
  paired-flattening proof. Its four flattening obligations are real, but manual
  synchronization through `nth_error` should be isolated behind a zip/`Forall2`
  API and point-uniqueness lemmas.
- `no_write_collision_implies_permutable` (126 lines) is the semantic core.
  Both directions are required, but collision transposition and the directional
  instruction-commutation argument should each be proved once.
- `permutable_instance_lists_preserve_semantics` (74 lines) is the cleanest
  high-level theorem in the file: it exposes the stable-sort proof idea. Keep
  this argument visible.
- The 305-line integer guard theorem is not intrinsically complex. Its WW, WR,
  and RW blocks duplicate the 103-line local abstraction used by the ordinary
  validator.
- The 105/109-line tiling/affine permutability theorems are two copies of one
  top-level decomposition; only the well-formedness checker differs.
- The 120-line well-formedness proof mostly reflects a long Boolean guard chain.
  Named projections can improve navigation, but a large portion of its linear
  size is expected unless the checker itself is represented compositionally.

## API-preserving remediation order

1. **P0: eliminate direct duplication with no theorem redesign.** Replace the
   PointWitness equality copies by exact aliases/wrappers. Move
   `forallb_imp_true_forall` before both access-helper proofs and use it to
   shorten `validate_two_accesses_helper_correct`. Preserve every exported
   AffineValidator name/type.
2. **P0: share the access-conflict proof kernel.** Parameterize the local
   `validated_access_checks_imply_no_write_collision` over the access-pair
   checker and its soundness theorem. Instantiate it for ordinary and integer
   feasibility. This turns the externally used 305-line band theorem into a
   short wrapper and prevents the two kernels from drifting.
3. **P1: clarify the paired-flatten core.** Add private forward-membership,
   backward-reconstruction, projection, and uniqueness lemmas around
   `compose_ipl_ext_at`; reuse `compose_pinstrs_ext_at_preserve_length`. Keep the
   two main flatten theorem names/statements unchanged.
4. **P1: factor semantic symmetry.** Prove one directional collision-to-
   execution-commutation lemma, then obtain the reverse direction using named
   access-list transpose/symmetry facts. Retain
   `no_write_collision_implies_permutable` unchanged.
5. **P1: unify affine and witness-aware top-level proofs.** Expose one accepted-
   validator specification or a refinement from affine acceptance to general
   acceptance. Make the duplicate correspondence, finiteness, permutability,
   and fixed-environment correctness results thin wrappers.
6. **P2: quarantine/delete old routes last.** The 44 unreachable declarations
   account for 627 proof-body lines. Remove only after an explicit out-of-tree
   compatibility decision; otherwise retain exact wrappers in a labeled legacy
   section.

## Proof hygiene

No `Admitted`, `Abort`, `Unshelve`, `dummy_state`, axiom, or conjecture occurs
in this file. Broad automation is frequent, but the principal readability risk
is duplicated explicit proof structure, not opaque search. No correctness defect
was established by this static audit.

## Generated evidence

- `/tmp/polcert-affinevalidator-declarations.csv`
- `/tmp/polcert-affinevalidator-declarations.md`
- `/tmp/polcert-affinevalidator-external-refs.txt`
- `/tmp/polcert-affinevalidator-rg-hits.txt`
- `/tmp/polcert-affinevalidator-long-proofs.md`
