# `src/ParallelValidator.v` declaration audit

## Scope and artifacts

The scanner strips nested comments and strings, inventories all top-level
declarations (including record projections), computes proof spans and lexical
dependencies/callers, follows discovered module aliases for qualified external
uses, and computes transitive reachability from repository-confirmed public
roots.

- `/tmp/polcert-parallelvalidator-declarations.csv`: declaration-level data,
  including dependencies and callers
- `/tmp/polcert-parallelvalidator-declarations.md`: sectioned readable table
- `/tmp/polcert-parallelvalidator-long-proofs.md`: every proof with at least 30 body lines
- `/tmp/polcert-parallelvalidator-external-refs.txt`: qualified external roots and bare-name evidence
- `/tmp/polcert-parallelvalidator-rg-hits.txt`: raw repository searches

## Inventory

- 68 declarations: 41 lemmas, 23 definitions, 2 records, and 2 record
  projections.
- 724 unique proof-body lines.
- 23 declarations have confirmed qualified repository-external uses.
- 59 declarations are transitively reachable from those public roots.
- 9 declarations, accounting for 83 proof-body lines, are not reachable from
  any confirmed repository root.
- 5 declarations are exact zero-reference declarations, accounting for 62
  proof-body lines.
- Only two proofs cross the 30-line threshold:
  `dot_product_select_coord` (45) and
  `check_pprog_parallel_currentb_sound` (333).

The public surface is intentionally broader than the final two soundness
lemmas:

- `Validator.v` re-exports the plan/certificate types, slice property,
  declarative safety property, checker, and soundness theorems.
- `ParallelCodegen.v` consumes `parallel_cert` and `certified_dim`.
- `JamValidator.v` reuses the program accessors, coordinate schedule row,
  prefix schedule, and checker guards.
- `TilingBandScheduleValidator.v` calls
  `ParallelCore.dot_product_select_coord` directly.

Consequently, ownership cleanup should keep current qualified names as
wrappers even when the canonical implementation moves.

## Core theorem chain

The file validates doall parallelism by reducing it to affine reversal
validation.

1. `parallel_old_pprog` replaces each statement schedule by the selected
   coordinate `d`.
2. `parallel_new_pprog` replaces it by the coordinate prefix strictly before
   `d`.
3. The checker validates this old-to-new affine rescheduling after checking
   dimension and input-view guards.
4. For two source instances in `same_parallel_slice d`, the new timestamps are
   equal while the old timestamps are distinct.
5. Whichever old timestamp is smaller therefore forms an old-strict/new-equal
   reversal.  `AffineCore.validate_implies_permutability` proves the pair
   commutes.
6. `eq_except_sched` transport moves commutativity from the synthetic points
   back to the original instances.
7. `checked_parallelize_current_sound` packages the validated dimension as a
   sound certificate.

This is a strong, readable proof idea.  It is obscured mainly by the single
333-line implementation proof, not by the declarative definitions.

## Ownership and duplication

### Parallel-validator core

Keep these concepts here:

- `parallel_plan`, `parallel_cert`, `parallel_safe_dim`, and certificate
  soundness;
- the old/new synthetic schedules and programs;
- current-coordinate slice predicates;
- executable guards/checker and their reflection lemmas;
- the synthetic-view timestamp formulas;
- the reversal-to-permutability correctness theorem.

### General semantic facts

The following three lemmas are not parallel-specific:

- `instr_point_sema_eq_except_sched_iff`
- `eq_except_sched_symm`
- `permutable_eq_except_sched`

`TilingBandScheduleValidator.v:917--997` contains effectively the same trio
under `_local` names.  Their natural owner is `InstanceListSema` or `PolyLang`,
where `eq_except_sched`, point semantics, and `Permutable` are defined.  Move
one canonical implementation there and keep both current modules' public names
as wrappers.  This removes duplicated semantic reasoning and gives future
validators one transport API.

`old_new_of_ext_eq_except_sched` is also a generic `PolyLang.InstrPoint_ext`
fact and belongs beside `old_of_ext`/`new_of_ext`.

### List and flattening infrastructure

- `nth_error_map_inv` duplicates versions in `TilingValidator`,
  `ISSRefinement`, and `Extractor`; `Misc.nth_error_map_iff` already provides
  the canonical equivalence.
- `nth_error_map_fwd` duplicates `TilingValidator.nth_error_map`,
  `ISSRefinement.nth_error_map_some`, and
  `TilingRelation.nth_error_map_some`.
- `in_old_of_ext_list_inv` and the unused `in_new_of_ext_list_inv` are direct
  specializations of `in_map_iff`.
- `rel_list_eq_except_sched_member` is generic membership transport for
  `rel_list`, built from `Base.rel_list_nth` and
  `Base.rel_list_implies_rel_nth`; the generic theorem belongs in `Base`.
- `flatten_instrs_member_inv`, `env_dim_of_flat_member`, and
  `current_coords_of_flat_member` are facts about `PolyLang.flatten_instrs`
  and instance shape.  Their canonical forms belong in `PolyLang`, with the
  current names retained as wrappers.

### Linear algebra

`dot_product_v0_app_1_nth` and `dot_product_select_coord` are one-hot vector
facts.  The latter is already used by the tiling-band validator through the
parallel module.  Canonicalize them in `LinalgExt`/`Linalg` and preserve the
current external path as a wrapper.

`seq_shift_succ` and `map_nth_seq_firstn` are generic list/index arithmetic and
belong in `ListExt`; the prefix-schedule product theorem remains
parallel-specific.

### Program accessors

`pprog_pis` and `pprog_varctxt` are generic projections from `PolyLang.t`, but
`JamValidator` and `LoopJamValidator` currently inherit them through this
module.  Adding canonical `PolyLang` accessors while retaining these aliases
would remove the ownership inversion without downstream churn.

## Dead and obsolete routes

Nine declarations are outside the confirmed public dependency closure.

### Obsolete well-formedness route: 64 proof lines

- `current_coord_schedule_row_cols`
- `exact_listzzs_cols_current_coord_old_schedule`
- `exact_listzzs_cols_current_coord_prefix_schedule`
- `wf_pinstr_affine_parallel_old_pi`
- `wf_pinstr_affine_parallel_new_pi`

The two `wf_pinstr_affine` theorems have no callers.  The current proof invokes
`AffineCore.validate_implies_permutability`, whose executable validator checks
the synthetic programs' affine well-formedness internally, so these lemmas are
not part of the soundness path.

### Unused direct old/new domain route: 8 proof lines

- `eqdom_parallel_old_new_pi`
- `rel_list_eqdom_parallel_old_new`

The live proof relates both views independently to the original program, so it
does not use a direct old-to-new `eqdom` list.

### Isolated unused wrappers: 11 proof lines

- `check_current_view_pinstrb_sound`
- `in_new_of_ext_list_inv`

The boolean program guard is live, but its per-instruction soundness lemma is
not.  Preserve these names until external compatibility is explicitly relaxed;
they are deletion/deprecation candidates, not proof-chain dependencies.

## The 333-line proof: intrinsic versus accidental complexity

The intrinsic argument consists of:

- one successful affine validation;
- one old/new extended-list correspondence;
- equality of prefix timestamps;
- inequality and total ordering of coordinate-`d` timestamps;
- one application of reversal permutability plus semantic transport.

The accidental complexity consists of:

- deriving source statements, old points, extended points, and new points
  twice, once per source instance;
- repeating mapped `nth_error` statements for old and new programs;
- repeating timestamp/current-coordinate lemmas for both points;
- converting `nth_error` inequality to bounded `nth` inequality inline;
- duplicating the final proof for the two possible coordinate orders;
- large positional calls to `validate_implies_permutability` and flattening
  correspondence theorems.

This should be factored, not tactic-golfed.  The file has only eight `eauto`
uses in total and no incomplete proof markers.

## Guard/API alignment finding

The main soundness proof discards the `check_current_view_pprogb` fact returned
by `check_pprog_parallel_currentb_true_inv`.  It also discards the global
`d < pprog_current_dim` fact, although the latter is used by the separate
dimension-range theorem.  Thus the current-view guard is stronger than what
`parallel_safe_dim` needs.

This is not automatically a bug.  The driver passes
`PolyLang.current_view_pprog pol`, and the guard can ensure that a direct call
to the public checker interprets `d` as a current structured-loop coordinate.
But that role is currently operational rather than reflected in the main
semantic theorem.  Before cleanup, choose one of two explicit designs:

1. Retain the guard and expose/consume its invariant at the driver/codegen
   boundary.
2. Document it as an intentionally conservative admission restriction beyond
   the `parallel_safe_dim` guarantee.

Do not silently remove it: `JamValidator` also reuses the guard.

## Remediation order with public names unchanged

### P0: canonical shared facts

1. Move `eq_except_sched` symmetry, point-semantic invariance, and permutability
   transport to `InstanceListSema`/`PolyLang`; retain wrappers here and in
   `TilingBandScheduleValidator`.
2. Replace local map/nth lemmas with `Misc`/`ListExt` canonical facts and keep
   compatibility wrappers.
3. Canonicalize the one-hot dot-product theorem in the linear-algebra library;
   retain `ParallelValidator.dot_product_select_coord` because it has a
   confirmed tiling-band caller.

### P1: factor the soundness theorem

1. Add a private single-point synthetic-view data lemma.
2. Add a private two-point lemma showing that `same_parallel_slice` forces a
   reversal in one orientation.
3. Factor the orientation-independent final transport into one lemma, using
   `Permutable_ext_symm` only for the reversed case.
4. Rewrite `check_pprog_parallel_currentb_sound` as the visible composition of
   those three facts.

Risk: medium.  The public theorem and executable checker remain unchanged, but
the helper must preserve exact correspondence among original, old, extended,
and new points.  Build the new proof alongside the old one before replacing it.

### P2: dead-route and ownership cleanup

1. Retain the nine unreachable names as wrappers initially; mark the obsolete
   well-formedness and direct old/new routes as compatibility-only.
2. Move flatten-member shape facts and program accessors to `PolyLang`, keeping
   aliases here.
3. After checking downstream/out-of-tree compatibility policy, decide whether
   the five zero-reference public lemmas should remain exported.

## Reader route after cleanup

1. `parallel_safe_dim`
2. `current_coord_old_schedule` and `current_coord_prefix_schedule`
3. `parallel_old_pprog` and `parallel_new_pprog`
4. `member_parallel_old_timestamp` and `member_parallel_new_timestamp`
5. the proposed private "same slice forces reversal" lemma
6. `check_pprog_parallel_currentb`
7. `check_pprog_parallel_currentb_sound`
8. `checked_parallelize_current_sound`

That route exposes the actual validation insight without requiring the reader
to traverse generic list plumbing or four copies of per-point witness recovery.

---

# `ParallelValidator.v` long-proof audit

Threshold: at least 30 proof-body lines.  Counts exclude `Proof.` and the
closing command.  The audited snapshot is the `proof/readability-cleanup`
worktree.

| Line | Declaration | Body lines | Ownership | Assessment | Recommended internal refactor |
|---:|---|---:|---|---|---|
| 493 | `dot_product_select_coord` | 45 | General linear algebra | The theorem states that a resized one-hot row selects coordinate `n`.  It is not specific to parallel validation and is already consumed externally by `TilingBandScheduleValidator.v:4789`.  The proof is correct and understandable, but spends most of its lines normalizing `resize`, lengths, and zero padding. | Move the canonical theorem and its helper `dot_product_v0_app_1_nth` to `LinalgExt` (or `Linalg` if that is the established home for one-hot/resize facts).  Keep `ParallelValidator.dot_product_select_coord` as an exact compatibility wrapper because it is a confirmed external API today. |
| 863 | `check_pprog_parallel_currentb_sound` | 333 | Core parallel-validator correctness | The theorem is central, but its size is not intrinsic.  The mathematical argument is short: for two instances in the same parallel slice, the synthetic old schedule is their differing coordinate `d`, while the synthetic new schedule is their equal prefix before `d`; one of the two old orders is strict and the corresponding new order is nondecreasing, so affine-validator reversal soundness yields commutativity.  Most lines build and synchronize source, old-view, extended, and new-view witnesses separately for each of two points. | Introduce private single-point view-data and two-point reversal lemmas.  Keep the public theorem statement unchanged and make the final proof explicitly compose guard inversion, view construction, reversal, affine permutability, and schedule-insensitive semantic transport. |

## Detailed decomposition of the 333-line soundness proof

The current proof has seven conceptual stages.

1. Invert `check_pprog_parallel_currentb` and retain the per-statement depth
   check plus successful affine validation.
2. Retimestamp the original flattening into the one-row old view and the
   prefix-schedule new view, obtaining the `eq_except_sched` relation to the
   original points.
3. For each original point, recover its source statement and prove `d` is
   within that statement's depth.
4. Invoke `AffineCore.validate_implies_permutability`, which supplies a shared
   extended point list connecting the old and new views and a theorem for
   every old-to-new schedule reversal.
5. For each of the two points, recover its extended witness, old/new
   memberships, source statement, timestamp formula, current-coordinate
   formula, and schedule-insensitive equality.
6. Convert `different_dim_at` from `nth_error` inequality to inequality of the
   selected coordinates, and convert the common prefix to equality of the new
   timestamps.
7. Split on the order of the selected coordinates.  In either orientation,
   build the old-strict/new-nondecreasing premises, use the affine theorem,
   and transport `Permutable` back to the original points.

Stages 2--5 are witness plumbing.  Stages 6--7 are the actual proof insight.
The source currently duplicates nearly every fact for `tau1` and `tau2`, and
the two final order branches repeat the same construction with arguments
swapped.

### Suggested private helper boundary

A private `parallel_view_point_data` proposition or existential lemma should
package, for one original point:

- its source `PolyInstr` and depth bound;
- its corresponding old-view point and `eq_except_sched` relation;
- its extended point and old/new memberships;
- its corresponding new-view point;
- the old timestamp as coordinate `d`;
- the new timestamp as prefix `firstn d`;
- the current-coordinate identities needed to transfer the slice premise.

Then prove a two-point lemma of the form:

```coq
same_parallel_slice d tau1 tau2 ->
parallel_view_point_data ... tau1 ext1 ->
parallel_view_point_data ... tau2 ext2 ->
(old_sched_lt ext1 ext2 /\ new_sched_ge ext1 ext2) \/
(old_sched_lt ext2 ext1 /\ new_sched_ge ext2 ext1).
```

The public soundness theorem would only select the orientation, apply the
affine reversal theorem, use symmetry in the reverse orientation, and apply
`permutable_eq_except_sched`.

## Guard use

`check_pprog_parallel_currentb_true_inv` exposes three pure guards and affine
success.  The main soundness proof uses:

- `all_pinstrs_cover_dimb`, to obtain `d < pi_depth` for each statement;
- affine-validator success, to obtain reversal permutability.

It does not use `check_current_view_pprogb`, and it does not use the global
`d < pprog_current_dim` fact.  The latter is separately consumed by
`checked_parallelize_current_implies_dim_in_range`.  The current-view guard has
no role in the stated `parallel_safe_dim` theorem, although it can still be an
intentional executable precondition ensuring that `d` denotes a structured
current-loop coordinate.  This should be resolved as a design decision:

- either expose/consume the current-view invariant at the driver/codegen
  interpretation boundary; or
- document that the guard is an operational restriction stronger than the
  semantic theorem.

Removing the guard solely because this theorem ignores it would change the
checker and also affect `JamValidator`, which reuses it.

## Automation and proof hygiene

- No `Admitted`, `admit`, `Abort`, `Unshelve`, `Axiom`, `Conjecture`, or
  `dummy_state` token occurs in the file.
- The entire file has only 8 `eauto`, 4 `auto`, and 23 `lia` occurrences.  The
  333-line proof has four `eauto` closing calls and a handful of local `lia`
  calls.  Broad tactic search is not the source of its size or likely compile
  cost.
- The highest-value change is theorem factoring and witness packaging, not
  replacing tactics line by line.
