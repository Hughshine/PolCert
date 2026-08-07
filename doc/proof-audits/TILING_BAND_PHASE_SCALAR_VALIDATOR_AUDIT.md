# Read-only audit summary: `TilingBandPhaseScalarValidator.v`

## Scope and evidence

- Source: 1,930 lines, 51 exported declarations, 29 proofs.
- Long proofs: seven inclusive `Proof.`--`Qed.` spans of at least 30 lines;
  each is reviewed in `/tmp/tiling_band_phase_scalar_long_proofs.md`.
- Declaration table: `/tmp/tiling_band_phase_scalar_declarations.csv` records
  source/proof spans, lexical dependencies and callers, qualified external
  uses, current repository reachability, role, ownership, and action.
- External repository roots are the runtime calls to
  `checked_tiling_sourceb_phase_scalar_direct` (`DirectRuntime:131`), its
  success inversion (`:202`), and same-context correctness theorem (`:457`).
  The last qualified use is split across source lines and must not be missed by
  a line-oriented scanner.
- Those three roots reach 50 of 51 declarations.  Only
  `nth_error_phase_scalar_layouts_inv` is outside the current repository
  runtime/correctness closure.  All declarations remain exported from the
  functor, so repository unreachability is not proof of external-API freedom.

This was a read-only audit.  No source change, build, or timing experiment was
performed.

## Reader path and theorem chain

### 1. Recognize phase classes and target shapes

`schedule_head_constant` reads a constant scalar row at the head of a source
schedule.  A `phase_scalar_entry` records that phase, whether the statement is
identity or tiled, the scalar-aware layout, and its tile sizes.

`infer_phase_scalar_shape_entries` walks source instructions, target
instructions, and witnesses together:

- an empty witness is an identity entry and must match the lifted source
  schedule up to target-side trailing-zero padding;
- a nonempty witness must infer a scalar-aware layout whose band starts after
  the scalar phase (`sabl_start = 1`), pass band selection, and match the
  rendered strip-mined schedule up to trailing-zero padding.

`check_phase_scalar_entries_consistentb` then requires statements in the same
scalar phase to be of the same kind; tiled members of a class must additionally
share a layout and tile-size recipe.  The soundness chain ends at
`infer_pprog_phase_scalar_shape_sound`.

### 2. Check active band components

`check_pprog_phase_scalar_components_direct` composes the extended
instructions, checks list alignment and access validity, and traverses every
component up to the maximum scalar layout length.  Pair checks are skipped for
different layouts or inactive dimensions; the semantic specification later
asks only about pairs with one common layout and an active component.

`check_pprog_phase_scalar_components_direct_sound` selects an arbitrary active
pair from those traversals and delegates the actual dependence/permutability
argument to
`Core.validate_two_instrs_scalar_aware_band_component_direct_sound`.  Thus this
module provides the class/layout traversal, while Core owns the pair checker.

### 3. Prove a reversal stays in one tiled phase class

`phase_scalar_entry_target_phase_decomposition` states the representation fact
used by the proof: both identity and scalar-aware tiled target timestamps begin
with the preserved scalar source phase.

`phase_scalar_reversal_same_class` then considers a pair ordered by the source
schedule but not by the target schedule.  Equal-length prefix reasoning forces
the phase scalars to agree.  Class consistency forces both entries to have the
same identity/tiled kind.  The identity case cannot reverse because each target
timestamp equals its source timestamp.  Therefore a real reversal is between
tiled entries with a common scalar-aware layout and equal tile sizes.

This theorem is the phase-scalar-specific insight.  The endpoint lookup and
timestamp plumbing around it should be factored, but the preserved-phase and
identity-impossibility argument should remain explicit.

### 4. Connect the direct checker to semantic equivalence

`checked_tiling_sourceb_phase_scalar_direct` requires, in order:

1. the common structural source/witness checker;
2. successful phase-scalar shape and class-consistency inference;
3. successful direct component checking.

`checked_tiling_sourceb_phase_scalar_direct_reordering_safe` classifies an
arbitrary reversal using the theorem above, supplies pair-local shape/layout/
recipe callbacks to Core's
`scalar_aware_pair_local_reversal_bridge_wf_with_env_len`, and discharges the
decreasing component with the checked componentwise property.  The final
`*_correct_same_ctxt` theorem feeds that reordering fact into the common tiling
semantic theorem and obtains source execution with `State.eq`-equivalent final
state.

There is no call to a general affine validator and no affine fallback on this
path.  The direct component checker is the acceptance argument; schedule-shape
recognition supplies the representation premises needed to interpret it.

## Main readability findings

### P0 proof hygiene: name the actual stages

The file has a useful top-level proof map but no section boundary between shape
inference (`34-740`), component checking (`742-1182`), reversal classification
(`1184-1592`), and public composition (`1594-1928`).  Add those four section
headings and the precise stage comments listed in the long-proof audit.  This
does not change declarations or module paths.

### P1 local factoring: remove repeated endpoint plumbing

Two local extractions have high readability payoff and do not change public
visibility:

- Before `check_pprog_phase_scalar_components_direct_sound`, add a helper that
  packages one selected endpoint's flattened slice membership,
  well-formedness, and valid-access fact.  It replaces the duplicated
  `1115-1173` block.
- Before `checked_tiling_sourceb_phase_scalar_direct_reordering_safe`, add
  `phase_scalar_tiled_shape_at`, deriving a scalar-aware entry shape from the
  selected entry/index/layout facts.  It replaces the nearly identical
  `Hshape_at1` and `Hshape_at2` blocks at `1747-1838`.

For `phase_scalar_reversal_same_class`, wait for the common Core endpoint-fact
package already motivated by many large tiling bridges.  Extend that package
locally with phase entry/head/timestamp observations rather than introducing a
second competing provenance record.  Preserve the proof core at `1425-1591`.

### P1 ownership: exact duplicates and misplaced representation facts

Seven declarations are duplicated nearly verbatim in
`TilingBandMixedSecondValidator.v`:

- `schedule_head_constant`, `pinstr_head_constant`;
- `forallb_zeqb_zero_dot_product`, `schedule_head_constant_sound`;
- `forallb_skipn_true`, `schedule_head_constant_lift`,
  `schedule_head_constant_lift_sound`.

Their canonical owner should be a small phase-schedule support module below
Mixed and PhaseScalar.  Keep definitions/theorem wrappers under both existing
module paths if public compatibility is required.

`scalar_aware_stripmine_expected_timestamp_prefix` specifies a constructor
owned by Core and should move beside that constructor behind a compatibility
wrapper.  `scalar_aware_band_layout_eqb_refl` likewise belongs beside Core's
layout equality checker.  The `nth_error` lemmas for `phase_scalar_layouts` are
generic map lookup facts; the inverse lemma is currently unused and should not
receive polishing before an API decision.

## Module boundary and incremental-build issue

The file imports and instantiates the entire mixed validator only to obtain
Core:

```coq
Module Mixed := TilingBandMixedSecondValidator PolIRs.
Module Core := Mixed.Core.
```

There is no other `Mixed.` reference in this file.  DirectRuntime then obtains
Mixed through `PhaseScalar.Mixed` and Core through `Mixed.Core`.  This nests the
large Core, Mixed, and PhaseScalar functors for module-path convenience.

A dependency-clean prototype would instantiate
`TilingBandScheduleValidator PolIRs` directly in PhaseScalar, and instantiate
Core, Mixed, and PhaseScalar independently in DirectRuntime.  However, removing
`PhaseScalar.Mixed` changes an exported nested module path; retaining that alias
also retains the costly instantiation.  This is therefore an explicit API
choice, not a no-risk cleanup.

Measure any throwaway prototype with the same container and job count:

1. isolated wall time and peak RSS for Core, Mixed, PhaseScalar, and
   DirectRuntime `.vo` files;
2. incremental rebuild after touching only Mixed and then only PhaseScalar;
3. clean full-build wall time, peak RSS, and `.vo` sizes;
4. the existing test suite and clean full `coqc` CI-equivalent build.

Do not add or use `coqchk`; the project gate is the clean full proof build and
existing CI/tests.

## Recommended order

1. Add section/stage comments without theorem changes.
2. Extract the two strictly Local helpers from component soundness and final
   reordering composition.
3. Reuse the common Core endpoint package in the 340-line same-class theorem.
4. Deduplicate phase-schedule facts and move Core representation facts behind
   wrappers.
5. Decide whether the unused inverse lookup theorem and nested `Mixed` path are
   compatibility obligations.
6. Only then time a direct-functor prototype.

The active proof has the right semantic layering.  Its problem is that
phase-class reasoning is hidden among repeated selected-endpoint bookkeeping,
not that the checker falls back to a different correctness algorithm.


---

# Long-proof audit: `TilingBandPhaseScalarValidator.v`

Criterion: inclusive `Proof.` through `Qed.` span of at least 30 lines.  The
current source has 29 proofs; seven meet the criterion.

## `check_phase_scalar_entries_consistentb_sound` (`298`, proof `302-332`, 31 lines)

**Purpose.** Lifts the triangular pairwise Boolean scan to
`phase_scalar_entries_consistent`: entries with an equal scalar phase have the
same identity/tiled kind, and tiled entries have equal layouts and tile sizes.

**Proof phases.** `303-309` performs list induction and splits the two Boolean
premises.  `310-331` handles the four ways in which the selected pair can lie at
the head or in the tail; the third case reverses the equality and then reverses
the returned layout/size equalities.

**Assessment.** The length is caused by the asymmetric triangular scan, not by
tiling semantics.  The proof is routine and readable once the four membership
cases are announced.  A higher-order generic pairwise-consistency scanner would
save little and make the payload invariant harder to read.

**Low-risk change.** Add a stage comment before `310` saying that the four
branches are `(head,head)`, `(head,tail)`, `(tail,head)`, and `(tail,tail)`.
Do not extract a helper solely for `320-330`; it is used once.

## `infer_phase_scalar_shape_entries_sound` (`334`, proof `340-419`, 80 lines)

**Purpose.** Proves that successful lockstep inference over source
instructions, target instructions, and witnesses constructs the inductive
`phase_scalar_shape_entries` relation.

**Proof phases.** `341-353` rejects mismatched list arities.  `354-377` handles
an identity witness: constant phase head, empty links, and the trailing-zero
schedule check.  `378-418` handles a tiled witness: inferred scalar-aware
layout, required start at one, selected band, rendered target schedule, and the
recursive tail.

**Assessment.** This is a direct soundness proof for a branch-heavy parser.  Its
case structure intentionally mirrors `infer_phase_scalar_shape_entries` at
`144-219`; compressing the destructs with automation would make auditability
worse.  There is no repeated semantic argument inside the proof.

**Low-risk change.** Insert three comments at `341`, `354`, and `378` naming
arity checking, the identity case, and the scalar-aware tiled case.  A stronger
refactor would change the executable definition to return a more structured
sum, but that is not justified for readability alone.

## `scalar_aware_stripmine_expected_timestamp_prefix` (`583`, proof `596-638`, 43 lines)

**Purpose.** Shows that when a scalar-aware layout starts at schedule row one,
the rendered target schedule preserves the first row of the lifted source
schedule as a prefix.

**Proof phases.** `599-628` exposes the local components of
`scalar_aware_stripmine_schedule_after_env` and resolves the rendered tile
prefix.  `629-637` substitutes the successful result, uses `sabl_start = 1`,
and observes that either an empty or nonempty lifted schedule has the required
decomposition.

**Assessment.** The theorem is conceptually small; most lines reproduce the
implementation's local `let` bindings.  Because it specifies a constructor
defined in Core, its canonical ownership is beside
`scalar_aware_stripmine_schedule_after_env` in
`TilingBandScheduleValidator.v`, not in the phase-class client.

**Refactor.** Add the canonical prefix theorem in Core and keep the current
name as a short compatibility wrapper.  If no move is made, add a comment before
`599` that the following names merely expose the constructor's `let` bindings;
there is no need for a new Local helper in this file.

## `phase_scalar_entry_target_phase_decomposition` (`664`, proof `678-713`, 36 lines)

**Purpose.** Gives the common semantic view needed by the phase argument: the
target timestamp is equal, modulo symmetric trailing-zero padding, to the
preserved one-row source phase followed by a remainder.

**Proof phases.** `680-699` handles a tiled entry using the scalar-aware prefix
theorem and the stored target-shape certificate.  `700-712` handles an identity
entry by choosing `skipn 1` as the remainder and applying `firstn_skipn`.

**Assessment.** This is a genuine and well-sized semantic bridge.  The two
cases are the point of the theorem.  It should remain visible and should not be
hidden behind broad automation.

**Low-risk change.** Add one comment per constructor branch.  If the preceding
prefix theorem moves to Core, keep this theorem in PhaseScalar because it
combines the two phase-class variants.

## `check_pprog_phase_scalar_components_direct_sound` (`996`, proof `1009-1182`, 174 lines)

**Purpose.** Converts successful all-layout/all-component checking into
`pinstr_list_phase_scalar_componentwise_permutable` by selecting an arbitrary
active pair and invoking Core's proved scalar-aware pair checker.

**Proof phases.** `1010-1043` opens alignment and valid-access checks.
`1044-1069` specializes the property to a flattened pair and reconciles `env`
with `envv`.  `1070-1105` finds the two combined `(instruction,layout)` entries,
selects the requested component from the all-component traversal, and selects
the pair from the all-pairs traversal.  `1106-1114` discharges equal-layout and
active-dimension Boolean guards.  `1115-1173` repeats endpoint slice,
well-formedness, and valid-access recovery for `ip1` and `ip2`.  `1175-1181`
calls `Core.validate_two_instrs_scalar_aware_band_component_direct_sound`.

**Assessment.** The proof is mostly checker traversal and endpoint plumbing;
the pairwise collision/permutability argument is correctly delegated to Core.
The repeated endpoint block is the only substantial local readability defect.
This also matches the broader Core audit: `flatten_instrs_ext_member_slice_local`
and four `Forall_nth_error` applications recur across several checker proofs.

**Low-risk extraction point.** Immediately before this theorem, add a `Local`
helper taking `pis`, `flat`, `ip`, `pi`, the flattening/membership/nth facts, and
the `Forall` well-formedness/valid-access facts, and returning one `slice` plus
slice membership, `wf_pinstr_ext_tiling`, and `valid_access_function`.  Replace
`1115-1173` with two helper calls.  Keep all existing public definitions and the
soundness theorem unchanged.  Add stage comments before `1028`, `1044`, `1082`,
and `1115` even if the helper is deferred.

## `phase_scalar_reversal_same_class` (`1218`, proof `1253-1592`, 340 lines)

**Purpose.** Establishes the central phase-class fact.  If source order is
strict but target order is not, the two instances must belong to a common tiled
phase class; identity entries cannot form such a reversal.  It returns the two
witnesses, entries, common layout, and equal tile-size recipes needed by the
scalar-aware local bridge.

**Proof phases.** `1258-1272` extracts source/witness invariants and transports
the environment length.  `1273-1292` recovers source instruction, target
instruction, witness, and timestamp provenance for each endpoint.  `1293-1329`
uses list-length alignment to prove that corresponding phase entries exist.
`1330-1390` recovers entry shapes, constant heads, and old/new timestamp
equations.  `1391-1424` rewrites target timestamps into preserved phase prefix
plus remainder.  `1425-1507` uses the reversal and equal prefix length to prove
the two scalar phases are equal.  `1508-1569` applies class consistency and
rules out the identity/identity case because its target comparison equals its
source comparison.  `1570-1591` returns the common tiled layout and equal
witness tile sizes.

**Assessment.** The underlying argument is important and should stay visible:
reversal preserves the scalar class, and identity work cannot reverse.  The
proof's size comes mainly from building the same endpoint observation twice and
from representing aligned-list lookup failure by two manual `nth_error_None`
contradictions.  It is not primarily tactic slowness or difficult arithmetic.

**Refactor.** After the common Core endpoint-fact package proposed by the main
tiling audit exists, introduce a `Local` phase-scalar endpoint observation
record/helper that adds the selected `phase_scalar_entry`, its shape/head, and
the four timestamp equations.  Use it twice in place of `1273-1424`.  As a
smaller independent step, add a generic aligned-list lookup lemma and replace
`1298-1329`.  Preserve `1425-1591` as the named proof core.  Until extraction,
add phase comments at `1258`, `1273`, `1293`, `1330`, `1391`, `1425`, `1508`,
and `1570`.

## `checked_tiling_sourceb_phase_scalar_direct_reordering_safe` (`1651`, proof `1667-1886`, 220 lines)

**Purpose.** Composes the source/shape/component checkers with the same-class
reversal theorem and Core's scalar-aware pair-local reversal bridge to prove
program-level tiling reordering safety.

**Proof phases.** `1670-1733` inverts the public checker, derives shape and
source facts, constructs composed-instruction well-formedness, and obtains the
componentwise permutability certificate.  `1734-1746` classifies an arbitrary
reversed pair.  `1747-1838` builds two nearly identical callbacks proving the
selected endpoints have the scalar-aware shape required by Core.  `1839-1868`
builds common-layout and common-recipe callbacks.  `1869-1885` invokes Core's
pair-local bridge and discharges its active component with the earlier checker
certificate.

**Assessment.** The high-level composition is correct and appropriately uses
the direct permutable-band checker as the acceptance argument.  The duplicated
`Hshape_at1`/`Hshape_at2` callbacks obscure the five-stage composition.

**Low-risk extraction point.** Before this theorem, add a `Local`
`phase_scalar_tiled_shape_at` helper parameterized by the selected index,
selected entry, its `pse_identity = false`, the phase-shape relation, and the
entry/layout nth facts.  It should return `Core.scalar_aware_entry_shape` for
arbitrary matching before/after/witness/layout values.  Replace `1747-1838`
with two applications.  This preserves every public type and removes roughly
70-80 proof lines.  Add stage comments before `1670`, `1695`, `1720`, `1734`,
`1839`, and `1869`.

## Priority

1. Extract `phase_scalar_tiled_shape_at` from the final composition theorem.
2. Extract the endpoint slice/wf/access helper from component-checker soundness.
3. Reuse the planned Core endpoint package in `phase_scalar_reversal_same_class`.
4. Move the scalar-aware prefix representation theorem to Core behind a wrapper.
5. Add phase comments to the two branch-mirroring soundness proofs.

The first two are local and low risk.  The third should be coordinated with the
larger Core/Mixed refactor so the project does not acquire another competing
endpoint record.
