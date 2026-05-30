# Storage-Aware Validation Overview

This is the entry point for the storage-generalization notes.  The goal is to
state the problem cleanly before choosing a mechanization strategy.  The current
verified PolOpt pipeline remains the identity storage case:

```text
same logical statement instances
same logical storage accesses
different schedule, grouping, order, or loop annotation
final relation: State.eq
```

The transformations studied here go beyond that case.  They may add dynamic
instances, duplicate work, introduce helper copies, allocate private storage,
remap layout, reuse physical cells, or commit only selected target writes.  The
correctness statement must therefore say what the target execution represents
and what the surrounding context can observe.

## Document Map

- `POLYHEDRAL_TRANSFORMATION_TAXONOMY.md` classifies transformation families by
  instance relation, storage relation, and final observation.
- `STATE_VIEW_RELATION_DESIGN.md` defines the intended role of `State.eq` as
  the identity state view and sketches view constructors for storage-aware
  relations.
- `STORAGE_GENERALIZATION_PLAN.md` records a possible proof-engineering route
  for extending PolCert without weakening the current `State.eq` route.
- `FRAGMENT_TO_CONTEXT_CORRECTNESS_GAPS.md` separates PolIR fragment theorems
  from future C/CompCert contextual correctness obligations.
- `experiments/storage-validation-standalone/` contains finite executable
  models of candidate witnesses.  They are sanity checks for obligation shapes,
  not verified validators.

## Current Status

In this host worktree, the storage-generalization material is documentation,
the standalone executable experiment package, and uncommitted Coq skeletons.
The intended top-level theorem is still a semantic refinement statement:
checked storage-aware transformation plus an input public-view relation implies
target executions are matched by source executions whose final states agree
under an output public-view relation.  The storage-specific witnesses
(private-cell separation, bounds, value flow, copy discipline, non-escape, and
commit policy) should remain premises discharged by validators, not the
primary relation that downstream composition has to understand.
The final theorem surface should therefore not expose the internal
`checked_parameterized_view_transform_family` machinery.  That machinery is the
certificate layer used to prove one simple relation-first endpoint:
`semantic_refinement_between Rpre Rpost source target`.  This is just the direct
semantic-refinement statement: every target execution from a state related to
the source input by `Rpre` has a matching source execution whose final state is
related by `Rpost`.  The existing schedule-only theorem is recovered by choosing
the same-state input relation and the `State.eq` output relation;
`TransformContract.semantic_refinement_between_same_state_iff_refinement_under`
and
`StateView.semantic_refinement_under_identity_views_iff_refinement_under_state_eq`
record that equivalence.  `semantic_refinement_under_views input_view
output_view source target` is only the compatibility instance where `Rpre` and
`Rpost` are induced by packaged views.  `StateView.v` now provides generic single-pass
certificate wrappers for both the existing unparameterized view-transform
families and the newer parameterized storage families, plus pair-certificate
wrappers for two-pass compositions.  A feature-facing certificate theorem can
therefore hide either one family check or a two-pass intermediate program while
reusing one shared state-sound proof pattern.
The next presentation layer names that shared endpoint directly:
`Rpre` and `Rpost` are ordinary state relations, and a view-packaged theorem
uses `states_match` only as the readable state relation induced by a view:

```text
accepted certificate
input states match
target execution
---------------------------------------------------------------
matching source execution and output states match
```

The older `_state_sound` lemmas are compatibility/proof-engineering artifacts;
the intended top theorem is the `_semantic_refinement` spelling over
`semantic_refinement_between`.
The first implementation step is `StateView.v`, which packages endpoint
relations as views and wraps the existing affine/general validators as
`same_state_view -> identity_view` refinements.  It also exposes a small
relation-inclusion algebra (`view_included_refl`, `view_included_trans`, and
`compose_view_monotone`) so storage validators can compose endpoint views
without unfolding the underlying state relations.  The current layout skeleton
also exposes `related_cells_view` and a `layout_view`-level theorem, so the
layout prototype no longer bypasses the view endpoint.  The legacy
affine/general validators are available through the same certificate surface
via `affine_identity_view_certificate` and
`general_identity_view_certificate`; these instantiate the intuitive endpoint
with `same_state_view` on input and `identity_view`/`State.eq` on output.
`StateObservation.v`
now proves that observer-backed cell views compose through
`compose_cell_relation`, and its `compose_cell_view` constructor makes public
footprint composition explicit through a shared-intermediate-observable
compatibility condition.  `cell_view_transform_contract_compose` then bundles
this with same-instance access-remap composition and semantic
`view_refinement` composition, giving a first end-to-end theorem shape for
composing storage-aware passes.  It also defines `cell_view`, which records the public
source/target cells represented by a cell relation; `PrivateStorageValidator.v`
uses this to state the first private-erasure theorem shape.
`PrivateStorageWitness.v` adds the
first checkable private-erasure witness: finite target-private cells must be
included in a finite hidden-cell set, which proves they are outside the public
cell relation.  It also contains small proved checkers for duplicate-free
private-cell lists, concrete private read-after-write traces, and
access-function read-after-write traces that instantiate to concrete
`MemCell` traces for every dynamic point.  The concrete private trace route now
also checks that every trace read/write cell belongs to the declared
`private_cells` set, so use-def evidence cannot silently refer to cells outside
the hidden/separated storage region.  The access-function route also has a
finite instance-declaration witness: for a supplied finite point set, every
instantiated access trace cell must belong to the declared private cell set.
Composed with `StorageBoundsWitness`, the
private-boundary route can now show that every concrete private trace cell lies
within declared private-storage bounds.  It also factors out reusable finite
cell-set obligations such as private/public and private/frame disjointness.
`PrivateBoundaryWitness.v` adds the first boundary-copy layer for private
storage: required public live-ins must have copy-in pairs, required public
live-outs must have copy-out pairs, those pairs must use declared private cells,
public copy-out destinations must be unique, and an optional private-side
uniqueness checker prevents multiple boundary pairs from sharing the same
private cell.  It also adds a value-entry checker showing that copy-in/copy-out
public and private boundary values match for each aligned boundary pair.  The
derived projection facts expose both copy-in and copy-out sides separately:
each checked boundary-value list has the same length as its boundary-pair list,
and every boundary pair can be projected to a matching value entry with equal
public/private values.
Related skeletons include
`TransformContract.v`, `StateView.v`, `ViewPipeline.v`,
`StorageWitness.v`, `SourceNoAliasWitness.v`,
`FramePreservationWitness.v`, `FrameValueWitness.v`,
`FramePreservationValidator.v`, `StorageFrameFamilyCompose.v`,
`StateObservation.v`,
`LayoutWitness.v`, `LayoutRemapValidator.v`, `PaddingLayoutWitness.v`,
`StorageBoundsWitness.v`,
`PaddingLayoutValidator.v`, `PrivateStorageWitness.v`,
`PrivateBoundaryWitness.v`,
`PrivateStorageValidator.v`, `ScalarPromotionWitness.v`,
`ScalarPromotionValueWitness.v`, `ScalarPromotionValidator.v`,
`CopyProtocolWitness.v`, `CopyCommitWitness.v`,
`CopyInstanceWitness.v`,
`CopyProtocolValueWitness.v`,
`CopyProtocolValidator.v`, `ScratchpadCopyValidator.v`,
`ReuseConflictWitness.v`, `LifetimeConflictWitness.v`,
`ReuseValueWitness.v`, `StorageCompatibilityWitness.v`,
`InterArrayReuseWitness.v`, `InterArrayReuseValidator.v`,
`StorageReuseFamilyCompose.v`, `StorageCopyFamilyCompose.v`,
`ReuseStateView.v`, `StorageBoundaryView.v`, `ReuseConflictValidator.v`,
`InstanceProjectionWitness.v`,
`InstanceProjectionValidator.v`, `OverlapClosureWitness.v`,
`OverlapTilingValidator.v`, `StorageOverlapFamilyCompose.v`,
`VersionCommitWitness.v`, `VersionCommitValueWitness.v`,
`VersionCommitValidator.v`, `StorageVersionFamilyCompose.v`,
`ReductionMergeWitness.v`,
`ReductionMergeValueWitness.v`, `ReductionMergeValidator.v`,
`StorageReductionFamilyCompose.v`,
`PhaseSeparationWitness.v`, `PhaseValueWitness.v`,
`PhaseProjectionWitness.v`,
`PhaseSeparationValidator.v`, `StoragePhaseFamilyCompose.v`, and
`CStateObservation.v`.
`StateView.v` now uses top-level `generic_state_view` and
`generic_checked_parameterized_view_transform_family` carriers so independently
instantiated validators can share both the facade-level view type and the
parameterized family type instead of exporting incompatible functor-local
records.  `ViewPipeline.v` factors out the repeated composition pattern shared
by most storage validators: the existing general validator proves
`before -> source_view`, while the feature-specific pass supplies finite witness
obligations plus an explicit semantic `view_refinement` from `source_view` to
the storage-changing target.
`TransformContract.checked_relational_transform_family_pair_compose` and
`StateView.checked_view_transform_family_pair_compose` are the current generic
two-pass composition hooks: two checked passes compose by composing their input
and output relations/views, so feature checkers do not need bespoke end-to-end
theorems for every pass ordering.  `StateView` also has a parameterized variant
for storage passes whose checker soundness depends on extra witness parameters
and semantic side conditions; this is the generic home for facade theorems that
hide feature-specific contracts while still composing as public-view
refinements.  The single-pass certificate facade,
`checked_parameterized_transform_certificate_refines`, and the two-pass facade,
`checked_parameterized_family_pair_certificate_refines`, are the shared theorem
shapes for accepted storage certificates.  Their conclusions are
certificate-level refinement predicates: input states match under the
certificate's input view, the target executes, and the source has a matching
execution whose final state satisfies the certificate's output view.  The older
explicit-state helper theorem
`checked_parameterized_transform_certificate_semantic_refinement` remains
available for proof scripts that want the quantified states exposed.
`Validator.v` re-exports the same certificate-level definitions and theorems,
including the pair-certificate refinement facade, so downstream files do not
need to reach into `StateView.v` directly for the top theorem shape.
`CInstrScalarStorageFamilyCompose.v` adds the first concrete
scalar-storage composition theorem: bounded CInstr scalar privatization followed
by bounded CInstr scalar promotion yields a composed public-view refinement,
with both features' traces, bounds, compatibility, separation, and non-escape
facts kept in side conditions.  This theorem now goes through the generic
parameterized family composition hook and also has a
`public_semantic_refinement` facade, which is the intended shape for future
storage pass sequences.  It now also has a concrete accepted-certificate top
theorem,
`accepted_bounded_cinstr_scalar_storage_certificate_refines`, whose conclusion
is the certificate-level
`bounded_cinstr_scalar_storage_semantic_refinement`, an instance of the generic
pair-certificate refinement predicate.  This hides the intermediate program and
both CInstr family checks while keeping the statement as close as possible to
the old semantic-refinement theorem shape.  The expanded helper theorem
`accepted_bounded_cinstr_scalar_storage_certificate_semantic_refinement` remains
available for proof scripts that want the state variables explicitly.  The
generic private-storage layer now also exposes
`PrivateStorageValidator.private_bounded_declared_boundary_unique_compatible_non_escape_value_family`,
which packages private local use-def, boundary copy-in/copy-out, value,
compatibility, bounds, and non-escape obligations below the CInstr-specific
scalar wrapper.  `StoragePrivateFamilyCompose.v` composes that generic
privatization/storage-expansion family with bounded scalar promotion and states
the result as `public_semantic_refinement`.  It now also exposes the
accepted-certificate endpoint
`accepted_bounded_private_storage_certificate_refines`, whose conclusion is the
generic pair-certificate refinement predicate instantiated with private-storage
witnesses.  The expanded
`accepted_bounded_private_storage_certificate_semantic_refinement` remains for
scripts that want the states explicit.  The same facade shape now
covers the scratchpad/packing route through
`ScratchpadCopyValidator.scratchpad_copy_bounded_non_escape_family`: the
parameter record carries the helper-instance projection, copy protocol, commit
cover, public-to-local mapping, value trace, declared public/local cells, bounds,
storage specs, escaped-cell set, and source-view program, while the exported
theorem is still just public-view refinement.  `StorageCopyFamilyCompose.v`
checks that this copy-mediated family composes with bounded scalar promotion
through the same generic pair-composition hook, and states the composed endpoint
as `public_semantic_refinement`.  It now also exposes
`accepted_bounded_scratchpad_copy_certificate_refines` and
`accepted_declared_copy_protocol_certificate_refines`, so copy-mediated storage
passes share the same top theorem shape as scalar storage: accepted certificate,
input public view, target execution, and matched source execution under the
output public view.  The generic copy protocol itself is now also
packaged as
`CopyProtocolValidator.copy_protocol_declared_bounded_compatible_commit_mapping_value_family`,
so copy-in/local/copy-out bookkeeping can participate in the same composition
interface before the scratchpad-specific instance/private-storage wrapper is
added.  The overlap/private
recomputation route is now packaged the same way through
`OverlapTilingValidator.overlap_private_ordered_bounded_non_escape_family`,
which carries target projection, ordered tile-local closure, value equivalence,
private/commit writes, compatibility, bounds, and non-escape witnesses while
exporting only public-view refinement.  `StorageOverlapFamilyCompose.v` checks
the corresponding overlap-then-scalar-promotion composition and exposes the
endpoint as both `public_semantic_refinement` and the accepted-certificate
theorem `accepted_bounded_overlap_certificate_refines`, so the
instance-duplication route now has the same readable top theorem as the
storage-only routes.  The overlap value witness now also
has elimination lemmas that project the finite value table per duplicated or
internal target instance: every listed projected target has a corresponding
value entry whose target key matches and whose recomputed value equals the
represented source value.  The
array-expansion/version route now follows the same facade rule through
`VersionCommitValidator.version_commit_read_fully_bounded_non_escape_family`,
which carries commit selection, read-version selection, produced versions, value
evidence, compatibility, bounds, and produced-version non-escape while exposing
only public-view refinement.  The composition wrapper now also exposes
`accepted_bounded_version_commit_certificate_refines`, so array-expansion-style
versioned storage has the same accepted-certificate top theorem as copy,
private, reuse, and overlap routes.  The
only the public-view refinement endpoint.  `StorageVersionFamilyCompose.v`
checks version-then-scalar-promotion composition through the same generic hook
with the same paper-facing endpoint.  Its value witness now also exposes
elimination lemmas that turn the positional mapping/value-entry check into
direct facts: the mapping and value-entry lists have the same length, and every
selected version mapping entry has a corresponding value entry whose source and
version cells match and whose values agree.  Inter-array reuse now has the same
public-semantic composition theorem in addition to the lower-level
`view_refinement` theorem, so both cross-array sharing and general conflict-safe
reuse expose a matching top-level shape.
The reduction-privatization route is also packaged as
`ReductionMergeValidator.reduction_merge_commutative_bounded_non_escape_family`:
the parameter record carries chunks, private accumulator cells, merge order,
value fold evidence, finite carrier algebra witnesses, storage compatibility,
bounds, and non-escape, while `StorageReductionFamilyCompose.v` proves the same
reduction-then-scalar-promotion composition shape through
`public_semantic_refinement`.
The reduction value layer now also checks that accumulator-value evidence is a
precise snapshot of the merge order: value cells are duplicate-free, every
merged private accumulator has exactly one value entry, and every value entry
belongs to the merge order.  This prevents the reduction certificate from
silently relying on ambiguous lookup behavior in its fold evidence.
`StorageWitness.v` now has the analogous access-level composition hook:
`pprog_same_instance_access_remap_compose` composes two target-to-source
cell-relation remaps through the same intermediate access cells.  This keeps
the instruction/access witness layer aligned with the state-view composition
layer instead of forcing every storage pass sequence to define a fresh combined
access relation.
`PaddingLayoutValidator.v`, `ScalarPromotionValidator.v`,
`CopyProtocolValidator.v`, `ScratchpadCopyValidator.v`,
`InstanceProjectionValidator.v`, `OverlapTilingValidator.v`,
`VersionCommitValidator.v`, `ReuseConflictValidator.v`,
`ReductionMergeValidator.v`, `PhaseSeparationValidator.v`, and the
observer-backed layout/private validators now consume this shared spine.
The most concrete private route at this point is
`checked_access_bounded_declared_local_private_expansion_view_correct`: it
packages local private obligations over access functions, checks their finite
instantiations against declared private cells and private bounds, and composes
them with the still-explicit semantic refinement.  The most complete boundary route is
`checked_boundary_private_unique_value_expansion_view_correct`, which combines
live-in/live-out boundary copies, private-side boundary uniqueness, and aligned
boundary value evidence under the observer-backed private-erasure theorem.
The scalar-expansion route now treats source temporaries as part of the same
visibility discipline: pure expansion without copy-out must hide the expanded
source scalar cells as well as the target private cells, and
`ScalarExpansionValidator.scalar_expansion_view_event_source_cell_hidden`
exposes that per-event consequence.  Its top-level wrappers
`checked_pure_scalar_privatization_correct` and
`checked_bounded_pure_scalar_privatization_correct` present the intended
theorem shape directly: checked pure scalar privatization implies public-view
refinement, with the old source temporary and the new private cells both erased
from the endpoint observation.  `ScalarExpansionValueWitness.v` adds the next
finite semantic layer: each expansion write carries equal source/private
values, and each expansion read carries source/private values equal to the
current value of the selected private cell.  The
`checked_value_pure_scalar_privatization_correct` wrapper threads this
value-flow witness through the same public-view refinement statement.  The
bounded variant
`checked_bounded_value_pure_scalar_privatization_correct` keeps that readable
top theorem while also checking private bounds, storage compatibility, and
non-escape.  The generic scalar-expansion route now also exposes
`checked_bounded_value_pure_scalar_privatization_public_refinement` and
`scalar_privatization_bounded_value_family`, so the non-CInstr scalar
privatization core can participate in the same public-view family composition
interface.  `StorageScalarFamilyCompose.v` composes that generic
privatization/expansion family with the generic scalar-promotion family through
`public_semantic_refinement`.  It now also provides the first scalar-storage
certificate wrapper,
`accepted_bounded_scalar_storage_certificate_state_sound`, where the theorem
surface is the direct semantic-refinement shape: accepted certificate, input
public-view relation, target execution, and matching source execution with the
output public-view relation.  `CInstrScalarExpansionWitness.v` is the first concrete
instruction-facing bridge: paired CInstr assignment steps can justify one
expansion write/value event, and paired scalar access evaluations can justify
one expansion read/value event.  The bridge also exposes the underlying
`CInstr.semantics` steps for writes and gives read/write singleton value-flow
lemmas that work from an arbitrary current private-value map, which is the
shape needed for later pass-level trace composition.  It now also contains an
ordered trace witness: a list of CInstr-derived scalar-expansion reads and
writes threads the current private-value map through schedule order and proves
the generic scalar-expansion value-flow obligation, while separately exposing
that the trace events are mapped by the declared expansion entries.  Its
per-event bridge theorem now combines these two directions: every event in the
ordered CInstr-derived value trace is mapped by the declared expansion entries,
has the storage-event kind claimed by the value event, and carries equal
source/private values.  Direct corollaries now name the generic and
CInstr-derived write/read value equalities, so later simulation proofs do not
need to unfold the value-match predicate.  The trace now also exposes
event-level CInstr
provenance through
`cscalar_expansion_value_event_cinstr_semantics` and
`cscalar_expansion_value_trace_event_cinstr_and_matched`, so later pass-level
proofs can retrieve the local source/private CInstr read or write witness for
an arbitrary ordered trace event without redoing the trace induction.
`CInstrScalarExpansionValidatorBridge.v` connects this Prop-level CInstr trace
evidence to the scalar-privatization public-view wrappers: a checked storage
core plus an ordered CInstr trace can build the value-core obligations used by
the pure and bounded scalar privatization refinement theorems, without making
the final theorem expose the trace as its endpoint relation.  The cleaner
bridge wrappers derive the scalar-expansion event list directly from the
ordered value trace, so callers do not need to pass a separate event list plus
an equality proof.  The value-flow layer now also proves private use-def:
because a private read is legal only when its cell has a current value in the
threaded expansion map, the corresponding private trace is read-after-write
safe.  `ScalarExpansionValueWitness.v` now exposes this as
`scalar_expansion_value_obligations_private_use_def` and
`scalar_expansion_value_obligations_events_private_use_def`; it also exposes
`scalar_expansion_value_obligation_event_matched`, a per-event projection fact
that every checked write/read value event matches its storage-event kind and
has equal source/private values.  `Validator.v` re-exports these facts for
users of the storage facade.  The CInstr bridge uses this to offer a smaller
static-core theorem where
declared entries, hidden cells, and freshness are checked, while event mapping
and use-def come from the ordered CInstr trace.
The same static-trace route now has a bounded variant that adds private bounds,
source/private storage compatibility, and non-escape checks before returning
the bounded scalar privatization obligation package and the same public-view
refinement conclusion.  The bridge now also provides public-refinement-only
facade theorems for both the static and generic CInstr trace routes.  These
theorems deliberately hide the scalar-expansion contract records from the
composition-facing conclusion, so the endpoint remains the intuitive
public-view semantic refinement.  The bounded static CInstr route is now also
packaged as `cscalar_privatization_bounded_family`, an instance of
`StateView.checked_parameterized_view_transform_family`: the parameter record
carries the source-view program, hidden/private cells, entries, CInstr value
trace, bounds, compatibility specs, and non-escape set, while the family
interface exposes only the public input/output views and a `view_refinement`
soundness theorem.
The CInstr family is now explicitly layered on top of the generic
`scalar_privatization_bounded_value_family`; the former discharges the CInstr
trace-simulation side condition, while the latter is the reusable storage
semantics layer.
`SourceNoAliasWitness.v` makes the front-end memory abstraction explicit: each
logical source object has a duplicate-free finite footprint, object ids are
duplicate-free, different footprints are pairwise disjoint, and a finite list
of source read/write cells can be checked against those declared footprints.
It also exposes entry-level corollaries: distinct source objects have disjoint
declared footprints, and covered access entries for distinct source objects
therefore cannot share a concrete source cell.
This remains a precondition witness rather than a transformation theorem.
`FramePreservationWitness.v` adds the generic contextual boundary condition:
fragment writes must be contained in an allowed-write set, and that allowed set
must be disjoint from frame cells owned by the surrounding context.
`FrameValueWitness.v` adds the corresponding finite value snapshot layer:
each context-frame cell is aligned with a before/after value pair and those
values must match.  The frame witnesses now expose direct projection facts:
checked writes are in the allowed-write set, checked writes are distinct from
frame cells, frame-value tables have the same length as the frame-cell list,
and each supplied frame-value entry preserves its before/after value.
`FramePreservationValidator.v` packages that side condition with the common
source-view theorem shape, so feature-specific storage views can carry a frame
contract without changing their final-state relation.  Its bounded value route
now also has a public-only facade and
`frame_preservation_bounded_value_family`; `StorageFrameFamilyCompose.v` checks
that this contextual frame family composes through the same
`public_semantic_refinement` interface as the storage-changing families.
`PaddingLayoutWitness.v` adds the finite allocation side of layout/padding:
source cells map functionally to target cells, target cells are injective and
allocated, and padding cells are duplicate-free, allocated, and outside the
represented target image.  `StorageBoundsWitness.v` adds the structured
in-bounds side: declared array extents are well formed, finite physical cells
can be checked against those extents, and padding/layout validators can require
all allocated physical cells to be within declared bounds.  Its derived
projections now recover the concrete array-bounds entry and per-dimension
index proof for a checked cell, so later pass-specific corollaries can cite the
actual declared extent rather than only the packed `cell_within_declared_bounds`
predicate.  `LayoutValueWitness.v` adds the boundary value side:
each source-to-target layout map entry can be paired with evidence that the
source logical value equals the represented target physical value.
`PaddingLayoutValidator.v` composes the structural, optional access-remap, and
optional value witnesses with the same view-refinement endpoint.  The access
variants reuse `LayoutWitness.check_pprog_array_rename_access_remapb_sound` to
check that target PolIR accesses use the declared array rename relation.  The
declared-layout route now also has a bounds-aware variant that composes
in-bounds evidence with declared access remapping, boundary values, and
size/alignment compatibility.
`ScalarPromotionWitness.v` starts the scalar-promotion route by checking the
local load/use/store protocol for a promoted source cell: scalar reads and
writes require a prior load, ordinary writes to the promoted source cell are
rejected as interference, and live-out promoted cells require a final store.
`ScalarPromotionValueWitness.v` adds the first value-flow layer over that
protocol: a load initializes the scalar to the source value, scalar reads see
the current scalar, scalar writes update it, and store-back commits the current
scalar value.  It now also exposes
`ScalarPromotionValueWitness.scalar_value_obligations_use_def` and
`ScalarPromotionValueWitness.scalar_value_obligations_events_use_def`, so the
value trace itself proves that scalar reads, scalar writes, and store-back
events occur only after the promoted scalar has a current value.  The value
trace now also supports arbitrary-event projection through
`ScalarPromotionValueWitness.scalar_value_obligation_event_matched`, recovering
the matching promotion-event kind and the load/store value equality carried by
the selected value event.  `CInstrScalarPromotionWitness.v` now connects this
value-flow layer to concrete CInstr semantics: load/read/write/store/global-write
events can be derived from CInstr access, expression-evaluation, and assignment
steps, and an ordered CInstr-derived trace proves the generic scalar-promotion
value-flow obligation.  It now also exposes
`cscalar_promotion_value_event_cinstr_semantics` and
`cscalar_promotion_value_trace_event_cinstr_and_matched`, so a later pass-level
proof can select an arbitrary trace event and recover both its CInstr
provenance and its promotion-specific kind/internal-value match facts.  The
load/store equality corollaries now name those selected-event value facts
directly for CInstr-derived traces.  The
bridge additionally exposes
`cscalar_promotion_value_trace_event_cinstr_and_generic_matched`, which phrases
the same selected-event fact using the generic scalar-promotion value witness
predicates.
`CInstrScalarPromotionValidatorBridge.v` connects that
CInstr trace evidence to the existing scalar-promotion view wrappers, including
the compatible and bounded/non-escape variants, without changing their
public-view refinement conclusion.  It also exposes public-refinement-only
facade theorems, so downstream composition can consume only the semantic
endpoint while the trace, compatibility, bounds, separation, and non-escape
proofs remain internal obligations.  Its bounded route is likewise packaged as
`cscalar_promotion_bounded_family`, so scalar promotion can participate in the
same parameterized public-view transform family interface as scalar
privatization.  The generic scalar-promotion core now has the same family layer:
`ScalarPromotionValidator.scalar_promotion_bounded_compatible_non_escape_value_family`
packages the finite protocol, value trace, storage compatibility, source/scalar
bounds, non-escape, and separation obligations below the CInstr bridge.  It
also exposes
`checked_scalar_promotion_bounded_compatible_non_escape_value_public_refinement`,
so the non-CInstr scalar/register promotion witness can be consumed through the
same public-view family interface.  `ScalarPromotionValidator.v` composes the
storage protocol, the optional value-flow witness, scalar-private separation,
and the remaining instruction-level semantic refinement.
`CopyProtocolWitness.v` starts the P4 route by checking finite copy-in,
local-read/local-write, and copy-out traces: local reads require earlier local
definitions, and copy-out destinations are committed at most once.
`CopyCommitWitness.v` adds exact copy-out boundary coverage for update-style
scratchpad transformations: the committed target cells must exactly cover the
expected observable target set.
`CopyInstanceWitness.v` aligns copy protocol events with projected helper
instances: copy-in/local events must be internal target instances, while
copy-out events must be commit-role target instances.
`CopyMappingWitness.v` adds the remapping-consistency layer for copy-mediated
local storage: the declared public-to-local map is injective on both sides, and
copy-in, local read/write, and copy-out events use that declared map.  It also
connects the map back to the declared local-buffer cell set, so local
separation and bounds checks apply to the cells actually used by the copy
mapping rather than to an unrelated list.  The strengthened declaration route
also connects mapping-public cells back to the declared public-cell set, so
public-side bounds and frame/visibility assumptions can be tied to the same
finite mapping.
`CopyProtocolValueWitness.v` adds the value-flow layer for the same protocol:
copy-in transfers source value to local value, local reads observe the current
local value, local writes update it, and copy-out commits the current local
value.  It now also exposes
`CopyProtocolValueWitness.copy_value_obligations_local_use_def` and
`CopyProtocolValueWitness.copy_value_obligations_events_local_use_def`: the
value trace itself proves that every local read and copy-out observes a local
cell that has already been filled by copy-in or local write.  Direct
projections
`CopyProtocolValueWitness.copy_value_obligation_copyin_values_equal`,
`CopyProtocolValueWitness.copy_value_obligation_copyout_values_equal`,
`CopyProtocolValueWitness.copy_value_obligation_trace_copyin_values_equal`,
and `CopyProtocolValueWitness.copy_value_obligation_trace_copyout_values_equal`
make the two boundary equalities explicit without changing the public
refinement theorem.  `CopyProtocolValidator.v` packages both the bookkeeping-only and
value-flow variants into composable `view_refinement` theorems under an
explicit instruction-level semantic refinement.  The same equalities are
forwarded through the declared/bounded/compatible copy contract, keeping the
strong facade convenient for concrete-code lifting without making those facts
new top-level refinement assumptions.
`ScratchpadCopyValidator.checked_scratchpad_copy_full_view_correct` lifts the
copy remapping and value-flow witnesses to the scratchpad/packing composition
layer together with instance projection, copy-out exact cover, helper-instance
roles, and local-buffer separation.  The bounded declared variant additionally
requires every mapping-local cell to be declared as a local buffer cell and
checks those declared local cells against array bounds.  The fully declared
variant checks both sides of the mapping and can derive bounds facts for both
the mapped public cells and mapped local cells.  The non-escape bounded route now
also has a public-refinement-only facade and a
`scratchpad_copy_bounded_non_escape_family` instance of the shared
parameterized view-transform family, so scratchpad/packing can participate in
the same top-level composition structure as scalar privatization, scalar
promotion, and inter-array reuse.
`ScratchpadCopyValidator.v` combines instance projection, copy protocol, and
local-buffer separation into one wrapper for scratchpad/packing-style
transformations.
`ReuseConflictWitness.v` starts the contraction/reuse route by checking finite
logical-to-physical reuse maps against conflict pairs: conflicting logical
values must not map to the same physical cell.  `LifetimeConflictWitness.v`
checks the preceding finite live-range obligation: every pair of overlapping
live intervals must be listed as a conflict, and conflict-safe reuse then
implies physical separation for all live overlaps.  `ReuseValueWitness.v` adds
a boundary value witness aligned with the logical-to-physical map: each
physical boundary value must equal the logical value it represents.  The
derived projection facts expose that the finite value evidence has the same
length as the reuse map and that each reuse-map edge has a corresponding value
entry with matching logical/physical cells and equal boundary values.  The
reverse projection is also exposed, so every supplied value entry can be tied
back to the concrete reuse-map edge it claims to witness.
`ReuseConflictWitness.v` also checks boundary coverage: every source-observable
live-out selected for final projection must be present in the reuse map.  It
now also exposes the physical image of a reuse map, so contraction-style
validators can connect every actually reused physical cell to declared storage
bounds rather than checking an unrelated cell list.
`StorageCompatibilityWitness.v` adds a finite size/alignment compatibility
checker for logical-to-physical storage maps.  This captures the explicit
storage-class side condition needed by contraction, inter-array reuse, packing,
and scratch/local-buffer reuse without pretending that the specs have already
been derived from C types.  It also exposes table-entry projections from the
lookup-based check: every successful spec lookup is tied to a concrete supplied
spec entry, and every compatible mapping edge can recover the logical and
physical spec entries whose size/alignment facts were checked.  The shared
corollaries now work directly from either the compatibility checker or a
`reuse_lookup` result, so pass-specific wrappers can recover the concrete
logical/physical spec entries without restating the lookup-to-entry argument.
`InterArrayReuseWitness.v` packages the inter-array reuse case without adding
a new primitive: it combines live-interval conflict cover, conflict-safe reuse,
and storage compatibility.  Its derived facts say that mapped live-overlapping
logical cells have distinct physical cells, therefore two distinct logical
cells that share one physical cell cannot overlap in their live intervals, and
each concrete reuse-map entry can be projected to the observer boundary
relation plus the checked logical/physical storage-spec entries.
`InterArrayReuseValidator.v` gives that composed finite witness the same
`view_refinement` endpoint theorem shape as the other storage features.  Its
bounded variant additionally requires the shared physical image of the reuse
map to lie inside declared buffer bounds, and its contract-level corollaries
project individual reuse-map entries to declared bounds and compatible specs.
The bounded route now also has a
public-refinement-only facade and a `bounded_inter_array_reuse_family` instance
of the shared parameterized view-transform family.  `StorageReuseFamilyCompose.v`
uses that family with bounded scalar promotion through the generic pair-compose
theorem, showing that a reuse-class storage pass and a scalar-storage pass can
compose as one public semantic refinement while still leaving the concrete
boundary projection as the supplied output view.  It now also exposes
accepted-certificate state theorems for both bounded inter-array reuse and
bounded conflict-safe reuse, so contraction/reuse joins scalar and copy storage
under the same direct endpoint shape.
`ReuseStateView.v` turns a boundary reuse map into an observer-backed reuse
projection view, and now also exposes a `cell_view` for a declared live-out
boundary whose target-public cells are exactly the mapped image.
`StorageBoundaryView.v` is the first shared endpoint wrapper for storage-backed
boundary maps: it combines `check_reuse_boundaryb_sound`,
`check_storage_compatibilityb_sound`, and the observer-backed boundary view into
one theorem, so layout, phase projection, reuse/contraction, and copy-out style
passes can share the same final-observation discipline when their live-outs are
represented by a finite logical-to-physical map.  Its contract-level projections
now expose the concrete endpoint facts directly: every listed observable source
cell has a target under the boundary cell relation, and that target can be tied
back to the checked logical/physical storage-spec entries.
`ReuseConflictValidator.v` composes the finite conflict
checker, the optional live-range cover checker, the optional storage
compatibility checker, and the value witness under the remaining semantic
refinement shape.  Its bounded variants compose those obligations with
`StorageBoundsWitness` and derive that every mapped physical target returned by
`reuse_lookup` is within the declared physical bounds.  They now also expose
contract-level entry projections for concrete reuse-map pairs and value
entries: a bounded/compatible/live value contract can recover the mapped
physical bound, the logical/physical storage specs, and the equal boundary
values for each supplied entry.  The strongest
bounded/compatible/live-conflict/value route is now also exposed as
`bounded_compatible_live_conflict_reuse_value_family`, so general contraction or
rolling-buffer reuse is no longer only a standalone validator theorem; it can
compose through the same parameterized public-view family interface as the
inter-array reuse facade.  `StorageReuseFamilyCompose.v` packages this route as
`accepted_bounded_conflict_reuse_certificate_state_sound`, an accepted-certificate
theorem with the direct public-view semantic refinement shape.
`InstanceProjectionWitness.v` starts the overlap/helper-instance route by
checking target-to-source projection and exact live-out commit cover.  It now
also names the exact-cover consequences that later overlap proofs need:
duplicate-free commits, liveout-to-commit and commit-to-liveout directions,
and liveout-in-domain.
`InstanceProjectionValidator.v` packages that witness into the same
`view_refinement` composition pattern.
`OverlapTilingValidator.v` specializes that route for overlapped tiling: one
theorem covers duplication with no materialized private storage, and one theorem
adds tile-private separation when halo/local buffers are represented in the
target state.  `OverlapClosureWitness.v` adds the finite local-dependence
closure and ordering side conditions: each tile dependency must be supplied
either by a tile live-in or by a computation projected inside the same tile, and
tile-produced values must appear before their consumers in the tile target
trace.  Recomputed-value equivalence remains an explicit semantic obligation.
The storage-aware overlap variant also composes role-to-write-cell evidence
with `StorageBoundsWitness`.  Its role-to-write witness now exposes the
positional table in both directions: targets and writes have matching length,
each projected target has a write entry, and each write points back to a checked
target.  Internal recomputation writes can then be checked within declared
tile-private buffer bounds and commit writes within declared public-output
bounds.
`VersionCommitWitness.v` starts the array-expansion/versioning route by
checking that each source live-out selects exactly one target version and that
selected versions are duplicate-free.  It also exposes the exact-cover
consequences as named lemmas: live-outs have selected versions, selected
sources are live-outs, selected versions belong to the version image, and both
finite images are duplicate-free.  `VersionCommitValueWitness.v` checks that
value evidence is aligned with the selected source/version cell pairs and that
every selected version value equals the represented source value;
`VersionCommitValidator.v` gives both variants the same compositional theorem
shape.  The bounded version-commit route composes this with
`StorageBoundsWitness`, so selected target versions are checked against
declared version-array bounds and any selected version related by the commit
cell relation is known to be in bounds.  `VersionReadWitness.v` also exposes
the produced-version image used by internal read-selection witnesses; the
read-selection table now projects each read entry back to the expected-read
list and to the concrete produced `(producer, version)` pair it selects.  The
read-value witness now projects its positional table in both directions, so
later concrete-read proofs can cite a matching value entry for a read selection
and recover the source/version value equality from a supplied value entry.
The fully bounded read/commit route now checks that every read-selected produced
version is within its declared version-array bounds as well as every committed
version.  Its fully bounded non-escape route now also projects those supplied
read-value entries to declared produced-version bounds and non-escape facts.
It also has a public-only facade
and a `version_commit_read_fully_bounded_non_escape_family`, so the versioned
storage/array-expansion case participates in the same parameterized
public-view family composition interface as scalar, copy, reuse, and overlap.
`ReductionMergeWitness.v` starts the reduction-privatization route by checking
chunk exact cover, private accumulator uniqueness, and merge-order cover;
it also exposes the exact-cover consequences as named lemmas for later
semantic proofs.
`ReductionMergeValueWitness.v` checks the narrower value-flow side: merge-order
cells are looked up in supplied accumulator values and folded with a supplied
merge operator to the claimed final value.  It also projects that finite value
table both ways: every merge-order accumulator has an explicit `(cell, value)`
entry with the corresponding lookup result, and every supplied accumulator
value entry is known to belong to the merge order.  `ReductionMergeValidator.v`
composes both variants while keeping the reduction algebra law explicit.  Its
bounded non-escape variant also threads `StorageBoundsWitness` through private
accumulators, so every private accumulator consumed by the merge can be shown
to lie within declared accumulator-buffer extents.  The commutative bounded
non-escape route now also has a public-only facade and a
`reduction_merge_commutative_bounded_non_escape_family`, so reduction
privatization/merge policy uses the same parameterized public-view family
interface as the other storage-changing routes.
`PhaseSeparationWitness.v` starts the double-buffering route by checking phase
read visibility, write/live disjointness, and next-live coverage;
`PhaseValueWitness.v` adds phase snapshot value flow: reads have entry values,
and every next-live value is either written in the phase or inherited from the
entry snapshot.  It also exposes table-entry projections: snapshot/read/next
value lookups can be recovered as concrete `(cell, value)` entries from the
finite value tables.  `PhaseProjectionWitness.v` checks the final-boundary
projection from source logical live-outs to the final phase-live physical
cells, with an optional value-equality layer for those projected cells.  It
also exposes the projection map as a target-to-source `cell_relation` and names
the exact-cover consequences used by later view proofs.
`PhaseSeparationValidator.v` composes these variants while keeping the
phase/swap semantic meaning explicit.  The phase value layer now exposes
snapshot elimination lemmas: cells in a checked phase-live snapshot have lookup
values, value snapshots are duplicate-free, value cells belong to the declared
snapshot cell set, and lookup facts can be projected back to concrete value
table entries for reads and next-live flow.  The projection value layer also exposes
per-projection elimination lemmas from the positional source-target value table.
Its bounded projection variant also connects final phase-live target cells to
declared buffer bounds and derives that every mapped target cell exposed by the
projection relation is in bounds.
The bounded phase-protocol variant separately exposes the finite image of all
entry-live, read, write, and next-live cells used by the phase trace, so the
protocol itself can be checked against declared buffer bounds before any final
projection is considered.  The strongest phase route now combines both sides:
final projection compatibility/bounds plus protocol-cell bounds and non-escape
are packaged as
`phase_projection_bounded_compatible_non_escape_value_family`, and
`StoragePhaseFamilyCompose.v` demonstrates composition with scalar promotion
using the paper-facing `public_semantic_refinement` facade.
`Validator.v` re-exports the observer-independent source no-alias, frame
preservation, padding layout, scalar promotion, copy, reuse, projection,
overlap, version commit, reduction merge, and phase separation/projection
checker/theorem
interfaces;
`CStateObservation.v`
exposes the C-like observer instances for layout, private storage, and reuse
views.
Treat these files as exploration until they are committed, reviewed, and
integrated through the normal proof build.

The current committed, stage-complete result remains the state-preserving
polyhedral pipeline on `end-to-end`.  The notes in this directory describe the
next family of correctness problems; they do not claim that storage-changing
optimizations are already covered by the existing theorem.

## Canonical Axes

Use these three axes when describing any new optimization.

| Axis | Questions |
| --- | --- |
| Instance relation | Does each target dynamic instance correspond to exactly one source instance, or are there partitions, duplicated halo instances, helper copy instances, or merged reduction instances? |
| Storage relation | Does the target use the same logical cells, an injective physical layout, fresh private storage, copy-mediated local buffers, non-injective reuse, or versioned cells? |
| Final observation | Does the final target state equal the source state, project through a layout map, erase private cells, expose committed writes, or merge private partial values? |

Do not choose a theorem shape from the optimization name alone.  For example,
overlapped tiling primarily changes the instance relation, while contraction
primarily changes the storage relation.  Scratchpad tiling changes both.

## Canonical Primitive Names

The standalone experiments use the following names as a vocabulary for proof
obligations.  The numbering is only for discussion; it should not become a Coq
API.

| Primitive | Obligation |
| --- | --- |
| P-1 no-alias memory abstraction | Logical source names used by the polyhedral model denote disjoint memory footprints, or aliasing is represented explicitly. |
| P0 instance bijection / exact cover | Target instances project to valid source instances and cover the source domain with the required uniqueness condition. |
| P1 role-based projection | Duplicated or helper target instances are classified, usually as internal, commit, copy, or merge roles. |
| P2 access-map refinement | Rewritten target accesses denote the intended source logical cells or values. |
| P3 fresh private storage | Target-private cells are fresh for their live ranges and every private read has an appropriate reaching definition. |
| P4 copy protocol | Copy-in/copy-out events are ordered correctly, local reads are covered, local accesses use the same remap, and local storage is fresh for its lifetime. |
| P5 scalar simulation | A scalar temporary simulates a promoted memory cell between entry load and exit store, with no interfering writes. |
| P6 conflict-safe non-injective reuse | Logical values that are live together cannot share the same physical cell. |
| P7 version selection and commit | The target write or version that becomes source-observable is selected correctly and committed exactly once. |
| P8 reduction merge | Private partial results are merged under the algebraic assumptions claimed by the semantics. |
| P9 phase separation | Phase, swap, or visibility witnesses prevent overwriting live data and explain which physical cells represent each logical phase. |
| P10 frame preservation | Fragment writes stay inside an allowed-write set that is disjoint from surrounding-context frame cells, and the frame snapshot is preserved. |

This list intentionally folds commit exactness into P7.  Earlier notes used a
separate P8 for commit exactness and shifted reduction/phase numbering; those
older numbers should not be used going forward.

## Mechanized Coverage Matrix

The current exploration branch has checkable witnesses for the following
primitive slices.  The rightmost column is the deliberately explicit semantic
gap; these are the obligations that should later be discharged by
feature-specific instruction or trace simulation proofs.

| Primitive | Current Coq hook | Checked now | Still explicit |
| --- | --- | --- | --- |
| P-1 no-alias memory abstraction | `SourceNoAliasWitness.check_source_no_aliasb_sound`; `SourceNoAliasWitness.check_source_no_alias_accessb_sound`; `SourceNoAliasWitness.check_source_no_alias_access_boundedb_sound`; `SourceNoAliasWitness.source_no_alias_footprints_disjoint`; `SourceNoAliasWitness.source_no_alias_footprint_cells_distinct`; `SourceNoAliasWitness.source_access_cell_covered`; `SourceNoAliasWitness.source_access_footprints_disjoint`; `SourceNoAliasWitness.source_access_cells_distinct`; `SourceNoAliasWitness.source_access_cell_within_bounds` | object ids and finite footprints are duplicate-free; distinct source-object footprints are pairwise disjoint, so concrete cells from different source objects are distinct; finite source access cells can be checked to lie inside the declared footprint for their logical object, so covered access entries for different source objects inherit the same disjointness; footprint cells can be checked against declared array bounds, so covered source access cells inherit in-bounds facts | deriving the finite access cells and proving they over-approximate real C accesses |
| P0/P1 projection and roles | `InstanceProjectionWitness.check_instance_projectionb_sound`; derived facts `InstanceProjectionWitness.instance_projection_target_source_in_domain`, `InstanceProjectionWitness.instance_projection_commit_target_liveout`, `InstanceProjectionValidator.instance_projection_contract_target_source_in_domain`, `InstanceProjectionValidator.instance_projection_contract_commit_target_liveout`, and `InstanceProjectionValidator.instance_projection_contract_commit_sources_nodup` | projected target instances are in the source domain; commit-role instances exactly cover live-outs; concrete target entries can directly recover their projected source-domain fact, and commit-role targets directly recover their source-liveout fact from the packaged contract | deriving projected target sets from concrete codegen |
| P1 local dependence closure | `OverlapClosureWitness.check_overlap_closureb_sound`; `OverlapClosureWitness.check_overlap_ordered_closureb_sound`; `OverlapClosureWitness.overlap_closure_dependency_consumer_in_targets`; `OverlapClosureWitness.overlap_closure_dependency_available`; `OverlapClosureWitness.overlap_ordered_closure_dependency_ordered`; contract projections `OverlapTilingValidator.overlap_closure_contract_dependency_consumer_in_targets`, `OverlapTilingValidator.overlap_closure_contract_dependency_available`, `OverlapTilingValidator.overlap_ordered_closure_contract_dependency_ordered`, and `OverlapTilingValidator.overlap_private_ordered_closure_contract_dependency_ordered` | every finite tile dependency consumer belongs to the tile's projected target sources; every dependency producer is supplied by a tile live-in or a projected computation in the same tile; in the ordered variant, tile-produced dependencies precede their consumers; packaged overlap contracts now expose the same per-dependency facts directly | deriving dependencies and trace order from concrete schedule/access semantics |
| P2 access-map refinement | `LayoutWitness.check_pprog_declared_layout_access_remapb_sound`; `StorageWitness.pprog_same_instance_access_remap_instrs_length`; `StorageWitness.pprog_same_instance_access_remap_source_instr`; `StorageWitness.pprog_same_instance_access_remap_target_instr`; `StorageWitness.pprog_same_instance_access_remap_write_accesses_nth`; `StorageWitness.pprog_same_instance_access_remap_read_accesses_nth`; `LayoutRemapValidator.checked_declared_layout_remap_correct`; `LayoutRemapValidator.checked_declared_layout_remap_relational_correct`; `LayoutRemapValidator.checked_declared_layout_remap_view_correct` | same-instance access-list remap through a single declared-layout interface covering same-index array rename, index permutation such as transpose, and affine-composed index rewrites such as linearization; the declared-layout access witness can now be packaged under the common source-view composition theorem in observation, relational, and view forms; the shared access-remap layer now exposes direct program/instruction projections for list length, source/target nth instruction matching, and nth write/read access relations | instruction-level value simulation for rewritten accesses; deriving layout declarations from generated code |
| P2 plus padding | `PaddingLayoutWitness.check_padding_layoutb_sound`; `PaddingLayoutWitness.padding_layout_boundary_obligations`; `PaddingLayoutWitness.padding_layout_mapping_pair_target_in_targets`; `StorageBoundsWitness.check_storage_boundsb_sound`; `LayoutWitness.check_pprog_declared_layout_access_remapb_sound`; compatibility hooks for the older rename/permutation/affine checkers; `LayoutValueWitness.check_layout_valueb_sound`; derived facts `LayoutValueWitness.layout_value_obligation_length_match`, `LayoutValueWitness.layout_value_obligation_mapping_entry_matched`, and `LayoutValueWitness.layout_value_obligation_entry_in_mapping`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `PaddingLayoutValidator.checked_padding_layout_declared_access_bounds_compatible_value_view_correct`; derived facts `PaddingLayoutValidator.padding_layout_value_entry_mapping_pair`, `PaddingLayoutValidator.padding_layout_value_entry_values_equal`, `PaddingLayoutValidator.padding_layout_declared_access_bounds_compatible_value_entry_mapping_pair`, `PaddingLayoutValidator.padding_layout_declared_access_bounds_compatible_value_entry_values_equal`, `PaddingLayoutValidator.padding_layout_mapping_pair_target_within_bounds`, `PaddingLayoutValidator.padding_layout_mapping_pair_compatible_specs`, `PaddingLayoutValidator.padding_layout_value_entry_target_within_bounds`, and `PaddingLayoutValidator.padding_layout_value_entry_compatible_specs` | target image is injective and allocated; padding is duplicate-free, allocated, and outside the image; the finite source-to-target layout map yields shared storage-boundary obligations for endpoint views; allocated physical cells can be checked against declared array extents; target/source access functions can be checked under one declared-layout witness; mapped source/target boundary values match and can be projected per layout-map edge into matching value entries, while every supplied value entry is tied back to the checked map and directly inherits source/target value equality; mapped physical layout cells can be required size/alignment-compatible with represented logical cells, and the full contract now projects both mapping-pair and value-entry bounds/compatibility facts | deriving value entries, storage specs, and declared bounds from concrete semantics and deriving layout declarations from generated code |
| P3 fresh private storage | `PrivateStorageWitness.check_private_separationb_sound`; private use-def checkers; `PrivateStorageWitness.check_private_trace_cells_declaredb_sound`; `PrivateStorageWitness.check_private_access_instances_declaredb_sound`; `ScalarExpansionWitness.check_scalar_expansionb_sound`; `ScalarExpansionWitness.scalar_expansion_events_same_key_same_private`; `ScalarExpansionValueWitness.check_scalar_expansion_value_traceb_sound`; `ScalarExpansionValueWitness.scalar_expansion_value_obligation_event_matched`; `ScalarExpansionValueWitness.scalar_expansion_value_trace_pair_event_in_events`; `CInstrScalarExpansionWitness.cscalar_expansion_value_trace_event_mapped_and_matched`; `CInstrScalarExpansionWitness.cassign_scalar_expansion_write_singleton_value_flow`; `CInstrScalarExpansionWitness.caccess_scalar_expansion_read_singleton_value_flow_from_current`; `ScalarExpansionValidator.checked_value_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_bounded_value_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_bounded_value_pure_scalar_privatization_public_refinement`; `ScalarExpansionValidator.scalar_privatization_bounded_value_family`; `StorageScalarFamilyCompose.bounded_scalar_privatization_then_scalar_promotion_public_semantic_refinement`; `StorageScalarFamilyCompose.accepted_bounded_scalar_storage_certificate_public_semantic_refinement`; `StorageScalarFamilyCompose.accepted_bounded_scalar_storage_certificate_state_sound`; `ScalarExpansionValidator.checked_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_bounded_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_scalar_expansion_view_correct`; `ScalarExpansionValidator.checked_scalar_expansion_bounded_compatible_non_escape_view_correct`; `ScalarExpansionValidator.scalar_expansion_view_event_source_cell_hidden`; `ScalarExpansionValidator.scalar_expansion_event_private_cell_within_bounds`; `ScalarExpansionValidator.scalar_expansion_event_private_cell_not_escaped`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateBoundaryWitness.check_private_boundaryb_sound`; `PrivateBoundaryWitness.check_private_boundary_private_uniqueb_sound`; `PrivateBoundaryWitness.check_private_boundary_valueb_sound`; `PrivateBoundaryWitness.private_boundary_value_obligation_copyin_length_match`; `PrivateBoundaryWitness.private_boundary_value_obligation_copyout_length_match`; `PrivateBoundaryWitness.private_boundary_value_obligation_copyin_pair_matched`; `PrivateBoundaryWitness.private_boundary_value_obligation_copyout_pair_matched`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `PrivateStorageValidator.checked_bounded_declared_boundary_private_unique_compatible_non_escape_value_expansion_view_correct`; `PrivateStorageValidator.checked_bounded_declared_boundary_private_unique_compatible_non_escape_value_expansion_public_refinement`; `PrivateStorageValidator.private_bounded_declared_boundary_unique_compatible_non_escape_value_family`; `StoragePrivateFamilyCompose.bounded_private_storage_then_scalar_promotion_public_semantic_refinement`; `PrivateStorageValidator.checked_access_bounded_declared_local_private_expansion_view_correct`; `PrivateStorageValidator.private_declared_trace_cell_within_bounds`; `PrivateStorageValidator.private_access_instantiated_trace_cell_within_bounds` | private cells are duplicate-free and disjoint from public/frame cells; private reads have prior writes; concrete private trace cells are declared private cells; access-function private traces can be instantiated over a finite point set and each instantiated cell must be declared private; scalar expansion entries map each `(source instance, source scalar cell)` key to a unique declared private cell, all expansion events use that declared mapping consistently, the source scalar cells being replaced must also be hidden from the public endpoint view for the pure no-copy-out case, the resulting private trace is write-before-read, scalar expansion value traces check that private writes store the source logical value and private reads observe a value equal to the represented source read, and each checked value event can be projected to a matching storage-event kind plus equal source/private values; ordered CInstr-derived value traces additionally project each trace event to declared-entry mapping, kind matching, and equal source/private values; CInstr assignment/access semantic steps can be connected to those write/read value events, and the checked pure-scalar-privatization wrappers state the public-view refinement theorem directly; scalar expansion can now also compose private bounds, source/private storage compatibility, non-escape, and value-flow evidence in one top theorem and one reusable public-view family, yielding per-event source-hidden, private in-bounds, and non-escaping private-cell corollaries; the new scalar-storage certificate layer instantiates the generic pair-certificate theorem from `StateView.v`, hides the intermediate program and pair of family checks behind accepted-certificate predicates, and exposes direct public-view semantic refinement and state-sound theorems; declared private cells can be checked against array bounds; required live-ins/live-outs have boundary pairs; live-out public commits are unique; boundary private cells can be required unique; boundary public/private values match, and both copy-in and copy-out value evidence can be projected per boundary pair into matching value entries with equal public/private values; boundary public/private cells can be required size/alignment-compatible; generic private storage can now package declared local use-def, boundary copy-in/copy-out, boundary values, compatibility, private bounds, and non-escape as a public-view family, then compose through `public_semantic_refinement`; non-escape, declared trace coverage, finite access instantiation, bounds, uniqueness, value evidence, and compatibility can be composed in private-erasure theorem shapes | deriving full instruction traces, finite point sets, boundary value entries, escaped-cell sets, declared bounds, storage specs, and expansion mappings from concrete expression and type semantics |
| P4 copy protocol | `CopyProtocolWitness.check_copy_protocol_wfb_sound`; `CopyCommitWitness.check_copy_commit_coverb_sound`; `CopyCommitWitness.copy_commit_boundary_obligations`; `CopyInstanceWitness.check_copy_instance_traceb_sound`; derived facts `CopyInstanceWitness.copy_instance_trace_obligations_length_match`, `CopyInstanceWitness.copy_instance_trace_obligation_target_event`, and `CopyInstanceWitness.copy_instance_trace_obligation_event_target`; `CopyMappingWitness.check_copy_mappingb_sound`; `CopyMappingWitness.check_copy_mapping_local_declarationb_sound`; `CopyMappingWitness.check_copy_mapping_declarationb_sound`; derived facts `CopyMappingWitness.copy_mapping_local_declaration_pair_local_declared` and `CopyMappingWitness.copy_mapping_declaration_pair_declared`; `CopyProtocolValueWitness.check_copy_value_traceb_sound`; `CopyProtocolValueWitness.copy_value_obligations_local_use_def`; `CopyProtocolValueWitness.copy_value_obligations_events_local_use_def`; derived facts `CopyProtocolValueWitness.copy_value_obligation_event_matched`, `CopyProtocolValueWitness.copy_value_obligation_event_entry`, `CopyProtocolValueWitness.copy_value_obligation_trace_event_entry`, `CopyProtocolValueWitness.copy_value_obligation_copyin_values_equal`, `CopyProtocolValueWitness.copy_value_obligation_copyout_values_equal`, `CopyProtocolValueWitness.copy_value_obligation_trace_copyin_values_equal`, and `CopyProtocolValueWitness.copy_value_obligation_trace_copyout_values_equal`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `CopyProtocolValidator.checked_copy_protocol_commit_mapping_value_view_correct`; `CopyProtocolValidator.checked_copy_protocol_commit_mapping_bounded_value_view_correct`; `CopyProtocolValidator.checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_view_correct`; `CopyProtocolValidator.checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_public_refinement`; `CopyProtocolValidator.copy_protocol_declared_bounded_compatible_commit_mapping_value_family`; `StorageCopyFamilyCompose.bounded_copy_protocol_then_scalar_promotion_public_semantic_refinement`; `StorageCopyFamilyCompose.accepted_declared_copy_protocol_certificate_public_semantic_refinement`; `StorageCopyFamilyCompose.accepted_declared_copy_protocol_certificate_state_sound`; `CopyProtocolValidator.copy_protocol_committed_target_within_bounds`; `CopyProtocolValidator.copy_protocol_mapping_public_within_bounds`; `CopyProtocolValidator.copy_protocol_mapping_local_within_bounds`; `CopyProtocolValidator.copy_protocol_declared_bounded_compatible_copyin_values_equal`; `CopyProtocolValidator.copy_protocol_declared_bounded_compatible_copyout_values_equal`; `CopyProtocolValidator.copy_protocol_declared_bounded_compatible_trace_copyin_values_equal`; `CopyProtocolValidator.copy_protocol_declared_bounded_compatible_trace_copyout_values_equal` | local reads are covered by prior local definitions; copy-out targets are duplicate-free and can exact-cover expected observable targets; committed public copy-out targets yield an identity storage-boundary map for shared endpoint views; copy protocol events align with internal/commit projected helper instances, and that positional role-alignment can now be projected in both directions between concrete helper-instance entries and copy events; public-to-local remap is injective and used consistently by copy/local events; mapping-local cells can be required to belong to the declared local-buffer set; the stronger declaration checker also requires mapping-public cells to belong to the declared public set, and concrete mapping pairs project to declared public/local cells; copy/local/commit value flow is consistent and itself implies the local fill-before-use discipline for local reads and copy-outs; checked value events can be projected back to concrete value-trace entries with matching copy-event kind and equal boundary values; copy-in/source-to-local equality and copy-out/local-to-target equality are available as direct projection facts, including through the strongest generic declared/bounded/compatible contract; generic copy protocol can package commit exact cover, remapping, value flow, declared public/local mapping coverage, public/local storage compatibility, and declared bounds for commit targets plus mapped public/local cells in one view theorem; the strongest generic copy route now has a public-only facade and parameterized family instance, so copy-in/local/copy-out protocols compose through the same `public_semantic_refinement` interface as the higher scratchpad wrapper; its accepted-certificate wrapper instantiates the generic pair-certificate theorem and exposes direct public-view semantic refinement/state-sound endpoints; committed targets inherit the expected-target bounds through exact cover, and mapped public/local cells inherit their declared bounds | deriving the trace, value trace, helper-instance list, storage specs, and declared commit/public/local bounds from concrete instruction semantics |
| P4 scratchpad/packing composition | `ScratchpadCopyValidator.checked_scratchpad_copy_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_instance_commit_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_bounded_fully_declared_compatible_full_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_public_refinement`; `ScratchpadCopyValidator.scratchpad_copy_bounded_non_escape_family`; `StorageCopyFamilyCompose.bounded_scratchpad_copy_then_scalar_promotion_refinement`; `StorageCopyFamilyCompose.bounded_scratchpad_copy_then_scalar_promotion_public_semantic_refinement`; `StorageCopyFamilyCompose.accepted_bounded_scratchpad_copy_certificate_public_semantic_refinement`; `StorageCopyFamilyCompose.accepted_bounded_scratchpad_copy_certificate_state_sound`; derived facts such as `ScratchpadCopyValidator.scratchpad_copy_full_copyin_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_full_copyout_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_full_trace_copyin_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_full_trace_copyout_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_copyin_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_copyout_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_trace_copyin_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_trace_copyout_values_equal`, `ScratchpadCopyValidator.scratchpad_copy_mapping_public_within_bounds`, `ScratchpadCopyValidator.scratchpad_copy_mapping_local_within_declared_bounds`, `ScratchpadCopyValidator.scratchpad_copy_mapping_local_not_public`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_mapping_pair_compatible_specs`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_mapping_pair_within_declared_bounds`, `ScratchpadCopyValidator.scratchpad_copy_non_escape_mapping_local_not_public`, `ScratchpadCopyValidator.scratchpad_copy_local_cell_not_escaped`, and `ScratchpadCopyValidator.scratchpad_copy_mapping_local_not_escaped` | projection, copy protocol, optional copy-out exact cover, optional copy-instance role alignment, public-to-local remapping, declared public/local coverage for mapping cells, copy value flow, local-buffer separation, public/local storage compatibility, declared public/local bounds, and optional local-buffer non-escape compose into `view_refinement`; the strongest scratchpad route now has a public-only facade and a parameterized family instance, so copy-mediated storage passes compose with scalar promotion through the generic public-view family theorem; the exported composition route also has a paper-facing `public_semantic_refinement` theorem; its accepted-certificate wrapper instantiates the generic pair-certificate theorem and exposes direct public-view semantic refinement/state-sound endpoints for scratchpad/packing; scratchpad contracts directly project copy-in/source-to-local equality and copy-out/local-to-target equality, including through the strongest non-escape contract; mapping-public and mapping-local cells lie within their declared bounds, mapping pairs inherit compatible public/local storage specs from the strongest non-escape contract, mapping-local cells are separated from public cells, every declared local-buffer cell can be required not to escape the fragment, and mapping-local cells inherit that non-escape fact | deriving the trace, value trace, helper-instance list, storage specs, declared bounds, escaped-cell sets, and full copy-mediated semantic simulation |
| P5 scalar simulation | `ScalarPromotionWitness.check_scalar_promotionb_sound`; `ScalarPromotionValueWitness.check_scalar_value_traceb_sound`; `ScalarPromotionValueWitness.scalar_value_obligations_use_def`; `ScalarPromotionValueWitness.scalar_value_obligations_events_use_def`; `ScalarPromotionValueWitness.scalar_value_obligation_event_matched`; direct load/store equality facts `ScalarPromotionValueWitness.scalar_value_obligation_load_values_equal` and `ScalarPromotionValueWitness.scalar_value_obligation_store_values_equal`; `CInstrScalarPromotionWitness.cscalar_promotion_value_trace_event_cinstr_and_generic_matched`; `ScalarPromotionValidator.checked_scalar_promotion_compatible_value_view_correct`; `ScalarPromotionValidator.checked_scalar_promotion_bounded_compatible_non_escape_value_view_correct`; derived facts `ScalarPromotionValidator.scalar_promotion_value_load_values_equal`, `ScalarPromotionValidator.scalar_promotion_value_store_values_equal`, `ScalarPromotionValidator.scalar_promotion_source_scalar_compatible_specs`, `ScalarPromotionValidator.scalar_promotion_bounded_value_load_values_equal`, `ScalarPromotionValidator.scalar_promotion_bounded_value_store_values_equal`, `ScalarPromotionValidator.scalar_promotion_bounded_source_scalar_compatible_specs`, `ScalarPromotionValidator.scalar_promotion_source_cell_within_bounds`, `ScalarPromotionValidator.scalar_promotion_scalar_cell_within_bounds`, and `ScalarPromotionValidator.scalar_promotion_scalar_cell_not_escaped` | load-before-use, no bypassing source write, live-out store-back; scalar value-flow consistency; value-flow itself implies scalar read/write/store-back only happen after the promoted scalar has a current value; checked load/store value events expose explicit source/scalar equality, and ordered CInstr-derived traces expose the same selected-event fact with local CInstr provenance; promoted scalar/register storage can be required compatible with the source cell and the contract now projects the matching source/scalar storage specs directly; source and promoted scalar cells can be checked against declared storage bounds; promoted scalar/register storage can be required not to escape the fragment | deriving the value trace, storage specs, declared source/scalar bounds, and escaped-cell sets from concrete expression/type semantics |
| P6 conflict-safe reuse | `LifetimeConflictWitness.check_live_conflictb_sound`; `ReuseConflictWitness.check_conflict_safe_reuseb_sound`; `ReuseConflictWitness.reuse_lookup_target_in_targets`; `ReuseConflictWitness.conflict_safe_reuse_boundary_obligations`; `ReuseValueWitness.check_reuse_valueb_sound`; `ReuseValueWitness.reuse_value_obligation_length_match`; `ReuseValueWitness.reuse_value_obligation_mapping_entry_matched`; `ReuseValueWitness.reuse_value_obligation_entry_in_mapping`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `StorageBoundaryView.checked_storage_boundary_refinement_correct`; `ReuseConflictValidator.checked_bounded_compatible_live_conflict_reuse_value_view_correct`; `ReuseConflictValidator.checked_bounded_compatible_live_conflict_reuse_value_public_refinement`; `ReuseConflictValidator.bounded_compatible_live_conflict_reuse_value_family`; `StorageReuseFamilyCompose.bounded_conflict_reuse_then_scalar_promotion_public_semantic_refinement`; `StorageReuseFamilyCompose.accepted_bounded_conflict_reuse_certificate_public_semantic_refinement`; `StorageReuseFamilyCompose.accepted_bounded_conflict_reuse_certificate_state_sound`; `ReuseConflictValidator.bounded_compatible_live_reuse_mapping_target_within_bounds`; `ReuseConflictValidator.bounded_compatible_live_reuse_mapping_pair_within_bounds`; `ReuseConflictValidator.bounded_compatible_live_reuse_mapping_pair_compatible_specs`; `ReuseConflictValidator.bounded_compatible_live_reuse_value_entry_mapping_pair`; `ReuseConflictValidator.bounded_compatible_live_reuse_value_entry_within_bounds`; `ReuseConflictValidator.bounded_compatible_live_reuse_value_entry_compatible_specs`; `ReuseConflictValidator.bounded_compatible_live_reuse_value_entry_values_equal`; `InterArrayReuseWitness.check_inter_array_reuseb_sound`; `InterArrayReuseWitness.inter_array_reuse_boundary_obligations`; derived facts `InterArrayReuseWitness.inter_array_mapping_pair_cell_relation`, `InterArrayReuseWitness.inter_array_mapping_pair_compatible_specs`, and `InterArrayReuseWitness.inter_array_lookup_compatible_specs`; `InterArrayReuseValidator.checked_bounded_inter_array_reuse_view_correct`; `StorageReuseFamilyCompose.accepted_bounded_inter_array_reuse_certificate_public_semantic_refinement`; `StorageReuseFamilyCompose.accepted_bounded_inter_array_reuse_certificate_state_sound`; `InterArrayReuseValidator.bounded_inter_array_reuse_mapping_target_within_bounds`; `InterArrayReuseValidator.bounded_inter_array_mapping_pair_within_bounds`; `InterArrayReuseValidator.bounded_inter_array_mapping_pair_compatible_specs`; `InterArrayReuseValidator.bounded_inter_array_overlap_mapped_distinct`; `InterArrayReuseValidator.bounded_inter_array_same_physical_not_live_overlap` | explicit live intervals cover all overlap conflicts; conflicting logical values do not map to the same physical cell; every mapped physical target is in the reuse-map image; every source in a conflict-safe reuse map, including the inter-array facade, is covered as a reusable boundary footprint; concrete inter-array mapping entries project to the observer boundary relation and to the compatible logical/physical storage-spec entries; boundary physical values equal represented logical values, and the value evidence can be projected per reuse-map edge into matching logical/physical cells with equal values, while each supplied value entry can also be tied back to the checked reuse-map edge; mapped logical/physical cells have compatible size/alignment specs; mapped physical cells can be checked against declared bounds, and generic contraction value entries now inherit the same per-entry bounds/spec/value facts that inter-array mapping pairs already expose; a finite boundary map can be turned into a shared observer-backed endpoint view; live conflicts, reuse, compatibility, bounds, and boundary values can be packaged in one contraction-facing view theorem; the general bounded live-conflict reuse route now has a public-only facade and parameterized family instance, so array contraction/rolling-buffer reuse can compose through the generic public-view family theorem; both conflict-safe reuse and inter-array reuse now instantiate the generic pair-certificate theorem and expose direct accepted-certificate semantic/state endpoints; inter-array sharing is the composed case where one physical cell cannot represent two simultaneously live logical cells, and its shared buffer cells can also be bounded; from the bounded inter-array contract, overlapping live intervals map to distinct physical cells, so same-physical sharing implies no live overlap | deriving live intervals, storage specs, declared physical bounds, and boundary values from schedule/access/type semantics |
| P7 version selection and commit | `VersionCommitWitness.check_version_commitb_sound`; derived facts such as `VersionCommitWitness.version_commit_liveout_selected`, `VersionCommitWitness.version_commit_selected_source_liveout`, and `VersionCommitWitness.version_commit_boundary_obligations`; `VersionReadWitness.version_read_selected_version_in_produced_versions`; `VersionCommitValueWitness.check_version_valueb_sound`; derived facts `VersionCommitValueWitness.version_value_obligation_length_match`, `VersionCommitValueWitness.version_value_obligation_mapping_entry_matched`, and `VersionCommitValueWitness.version_value_obligation_entry_in_mapping`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `VersionCommitValidator.checked_version_commit_bounded_compatible_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_bounded_compatible_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_fully_bounded_compatible_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_fully_bounded_compatible_non_escape_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_fully_bounded_compatible_non_escape_value_public_refinement`; `VersionCommitValidator.version_commit_read_fully_bounded_non_escape_family`; `StorageVersionFamilyCompose.bounded_version_commit_then_scalar_promotion_refinement`; `VersionCommitValidator.version_commit_value_entry_mapping_pair`; `VersionCommitValidator.version_commit_value_entry_cell_relation`; `VersionCommitValidator.version_commit_value_entry_values_equal`; `VersionCommitValidator.version_commit_value_entry_source_liveout`; `VersionCommitValidator.version_commit_value_entry_version_in_versions`; `VersionCommitValidator.version_commit_value_entry_compatible_specs`; `VersionCommitValidator.version_commit_value_entry_version_within_bounds`; `VersionCommitValidator.version_commit_selected_version_within_bounds`; `VersionCommitValidator.version_read_selected_version_within_produced_bounds`; `VersionCommitValidator.version_produced_version_not_escaped`; `VersionCommitValidator.version_read_selected_version_not_escaped` | selected source live-outs and selected target versions are duplicate-free and exactly covered; every live-out has a selected version; selected relation edges point back to live-outs; the selected mapping sources are covered as a reusable boundary-view footprint; read-selection entries select produced versions for their expected dynamic producers; selected-version value evidence matches the mapping, has the same finite length, and can be projected per mapping entry or per supplied value entry into matching source/version cells with equal values; supplied commit-value entries recover the reusable selection relation and inherit source-liveout, version-image, compatible storage-spec, and committed-version-bounds facts; selected physical versions can be required storage-compatible with represented source live-outs; committed selected versions and internal read-selected produced versions can both be checked against declared version-array bounds, with per-cell derived bounds facts; produced internal version cells can additionally be required not to escape, and target reads that select produced versions inherit that non-escape fact; the strongest version route now has a public-only facade and parameterized family instance, so versioned storage/array expansion composes through the same public semantic theorem interface as other storage passes | deriving selected-version values, produced-version read witnesses, storage specs, declared version-array bounds, escaped-cell sets, and concrete write/type semantics |
| P8 reduction merge | `ReductionMergeWitness.check_reduction_mergeb_sound`; `ReductionMergeValueWitness.check_reduction_value_mergeb_sound`; `ReductionMergeValueWitness.reduction_merged_accumulator_value_entry`; `ReductionMergeValueWitness.reduction_accumulator_value_entry_in_merge_order`; `ReductionAlgebraWitness.check_reduction_*_lawb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `ReductionMergeValidator.checked_reduction_merge_commutative_bounded_compatible_non_escape_value_view_correct`; `ReductionMergeValidator.checked_reduction_merge_commutative_bounded_compatible_non_escape_value_public_refinement`; `ReductionMergeValidator.reduction_merge_commutative_bounded_non_escape_family`; `StorageReductionFamilyCompose.bounded_reduction_merge_then_scalar_promotion_refinement`; `ReductionMergeValidator.reduction_accumulator_storage_mapping_pair`; `ReductionMergeValidator.reduction_value_entry_in_merge_order`; `ReductionMergeValidator.reduction_value_entry_private_accumulator`; `ReductionMergeValidator.reduction_value_entry_compatible_specs`; `ReductionMergeValidator.reduction_value_entry_within_bounds`; `ReductionMergeValidator.reduction_value_entry_not_escaped`; `ReductionMergeValidator.reduction_private_accumulator_within_bounds`; `ReductionMergeValidator.reduction_merged_accumulator_within_bounds`; `ReductionMergeValidator.reduction_private_accumulator_not_escaped`; `ReductionMergeValidator.reduction_merged_accumulator_not_escaped` | chunks cover the reduction domain; private accumulators and merge order are well formed; merge-order accumulator values fold to the claimed final value; every merge-order accumulator can be projected to an explicit accumulator value entry and lookup result, and every supplied accumulator value entry is known to belong to the merge order; a finite carrier can witness closure, associativity, commutativity, and identity laws; private accumulators can be required size/alignment-compatible with the public reduction cell; private accumulators can be required non-escaping and within declared accumulator-buffer bounds; every accumulator in the merge order inherits the same bounds and non-escape facts, and every supplied accumulator value entry now inherits private-accumulator membership, compatible storage specs, declared accumulator bounds, and non-escape facts directly; bookkeeping, value, algebra, compatibility, bounds, and non-escape evidence can be packaged in one view theorem; the strongest reduction route now has a public-only facade and parameterized family instance, so merge-policy transformations compose through the same public semantic theorem interface as storage-only passes | deriving accumulator values/storage specs/declared bounds and connecting finite-carrier laws to concrete C/FP semantics |
| P9 phase separation | `PhaseSeparationWitness.check_phase_protocolb_sound`; `PhaseSeparationWitness.phase_protocol_cells`; `PhaseValueWitness.check_phase_value_protocolb_sound`; `PhaseValueWitness.check_phase_value_protocolb_final_snapshot`; derived facts `PhaseValueWitness.phase_snapshot_cell_has_value`, `PhaseValueWitness.phase_snapshot_cell_value_entry`, `PhaseValueWitness.phase_reads_have_value_entry`, `PhaseValueWitness.phase_next_cell_value_flow_entries`, and `PhaseValueWitness.phase_snapshot_value_cell_in_cells`; `PhaseProjectionWitness.check_phase_projectionb_sound`; `PhaseProjectionWitness.check_phase_projection_valueb_sound`; derived facts `PhaseProjectionWitness.phase_projection_value_obligation_length_match`, `PhaseProjectionWitness.phase_projection_value_obligation_mapping_entry_matched`, and `PhaseProjectionWitness.phase_projection_value_obligation_entry_in_mapping`; `PhaseProjectionWitness.phase_projection_sources_covered`; `PhaseProjectionWitness.phase_projection_boundary_obligations`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `StorageBoundaryView.checked_storage_boundary_refinement_correct`; `PhaseSeparationValidator.checked_phase_separation_bounded_view_correct`; `PhaseSeparationValidator.checked_phase_separation_bounded_non_escape_view_correct`; `PhaseSeparationValidator.checked_phase_projection_bounded_compatible_value_view_correct`; `PhaseSeparationValidator.checked_phase_projection_bounded_compatible_non_escape_value_view_correct`; `PhaseSeparationValidator.checked_phase_projection_bounded_compatible_non_escape_value_public_refinement`; `PhaseSeparationValidator.phase_projection_bounded_compatible_non_escape_value_family`; `StoragePhaseFamilyCompose.bounded_phase_projection_then_scalar_promotion_public_semantic_refinement`; `PhaseSeparationValidator.phase_projection_value_entry_mapping_pair`; `PhaseSeparationValidator.phase_projection_value_entry_values_equal`; `PhaseSeparationValidator.phase_projection_value_entry_source_liveout`; `PhaseSeparationValidator.phase_projection_value_entry_target_final_live`; `PhaseSeparationValidator.phase_projection_value_entry_compatible_specs`; `PhaseSeparationValidator.phase_projection_value_entry_target_within_bounds`; `PhaseSeparationValidator.phase_protocol_entry_live_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_read_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_write_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_next_live_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_entry_live_cell_not_escaped`; `PhaseSeparationValidator.phase_protocol_read_cell_not_escaped`; `PhaseSeparationValidator.phase_protocol_write_cell_not_escaped`; `PhaseSeparationValidator.phase_protocol_next_live_cell_not_escaped`; `PhaseSeparationValidator.phase_projection_mapped_target_within_bounds` | reads are visible, writes do not overwrite live cells, next-live cells are covered, entry/read/write/next-live protocol cells can be required to lie within declared buffer bounds, and for fragment-private ping-pong/local phase protocols those same protocol cells can be required not to escape; next-live values come from phase writes or entry-live values, the checked value protocol yields a final snapshot matching final-live cells, every snapshot cell has a concrete value lookup, value-table cells are duplicate-free and belong to the snapshot cell set, and read/next-live value-flow facts can be projected back to concrete finite value-table entries; final source live-outs are exactly projected to final phase-live cells, projected boundary values match and can be projected per mapping entry or per supplied value entry, supplied projection value entries are tied back to concrete source/target mapping pairs, and those entries inherit source-liveout, final-live target, compatible storage-spec, and target-bounds facts; projected final phase cells can be required size/alignment-compatible with represented live-outs, projected final phase cells can also be checked against declared bounds, and the final projection now yields the shared reusable boundary-view obligations used by storage-backed endpoint relations; the strongest phase route packages protocol bounds/non-escape and projection compatibility/bounds/value evidence as one parameterized public-view family, and its composition example exports `public_semantic_refinement` rather than only the compact internal `view_refinement` connective | deriving the phase/swap projection, storage specs, declared buffer bounds, escaped-cell sets, and target code phase arithmetic |
| P10 frame preservation | `FramePreservationWitness.check_frame_preservationb_sound`; per-cell corollaries such as `FramePreservationWitness.frame_preservation_write_allowed`, `FramePreservationWitness.check_frame_preservationb_write_allowed`, `FramePreservationWitness.frame_preservation_write_not_frame`, and `FramePreservationWitness.check_frame_preservationb_write_neq_frame_cell`; `FrameValueWitness.check_frame_valueb_sound`; `FrameValueWitness.frame_value_obligation_length_match`; `FrameValueWitness.frame_value_entry_in_frame_cells`; `FrameValueWitness.frame_value_entry_preserved_from_obligation`; `StorageBoundsWitness.check_storage_boundsb_sound`; `FramePreservationValidator.checked_frame_preservation_value_view_correct`; `FramePreservationValidator.checked_frame_preservation_bounded_value_view_correct`; `FramePreservationValidator.checked_frame_preservation_bounded_value_public_refinement`; `FramePreservationValidator.frame_preservation_bounded_value_family`; `StorageFrameFamilyCompose.bounded_frame_preservation_then_scalar_promotion_public_semantic_refinement`; `StorageFrameFamilyCompose.accepted_bounded_frame_preservation_certificate_refines`; `FramePreservationValidator.frame_preservation_contract_write_allowed`; `FramePreservationValidator.frame_preservation_frame_cell_value_preserved`; `FramePreservationValidator.frame_preservation_frame_value_entry_in_frame_cells`; `FramePreservationValidator.frame_preservation_frame_value_length_match`; `FramePreservationValidator.frame_preservation_write_within_allowed_bounds`; `FramePreservationValidator.frame_preservation_frame_cell_within_bounds` | writes are included in the allowed-write set and this inclusion is available directly from either the checker or the packaged contract; allowed writes are disjoint from frame cells; each fragment write is therefore outside the context frame and distinct from any checked frame cell; aligned frame before/after values are equal for every listed frame cell, every supplied frame-value entry belongs to the checked frame, each supplied entry preserves its value, and the frame-cell/value-entry lists have matching length; allowed-write cells and context-frame cells can be checked against declared array bounds; fragment writes inherit the allowed-write bounds; the bounded value route now has a public-only facade and parameterized family instance, so contextual frame preservation can compose through the same public semantic theorem interface as storage transformations | deriving the write set, declared bounds, and frame snapshots from concrete instruction semantics |
| overlap-specific composition | `OverlapTilingValidator.checked_overlap_*_view_correct`; `OverlapValueWitness.check_overlap_valueb_sound`; derived facts `OverlapValueWitness.overlap_value_obligation_length_match` and `OverlapValueWitness.overlap_value_obligation_target_matched`; `OverlapStorageWitness.check_overlap_storageb_sound`; derived facts `OverlapStorageWitness.overlap_storage_entries_length_match`, `OverlapStorageWitness.overlap_storage_target_write_entry`, and `OverlapStorageWitness.overlap_storage_write_target_in_targets`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `OverlapTilingValidator.checked_overlap_private_ordered_closure_bounded_compatible_value_storage_view_correct`; `OverlapTilingValidator.checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_correct`; `OverlapTilingValidator.checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_public_refinement`; `OverlapTilingValidator.overlap_private_ordered_bounded_non_escape_family`; `StorageOverlapFamilyCompose.bounded_overlap_then_scalar_promotion_refinement`; `OverlapTilingValidator.overlap_internal_write_within_private_bounds`; `OverlapTilingValidator.overlap_commit_write_within_commit_bounds`; `OverlapTilingValidator.overlap_internal_write_not_escaped` | duplicated/internal instances project to source instances and commits are unique; optional tile-local closure and private separation; recomputed value evidence matches the finite projected-target list and can be projected per duplicated/internal target into a matching value entry with equal source/target values; internal writes target tile-private cells and commit writes target public commit cells, and the role/write table can be projected per target or per write; private/commit write-cell regions can be checked against declared bounds, role-specific writes inherit the corresponding bounds fact, and tile-private internal writes can be required not to escape the fragment; the strongest overlap/private route now has a public-only facade and parameterized family instance, so instance-duplication transformations compose through the same public-view family theorem as storage-only passes | deriving concrete recomputed values, target write cells, storage specs, declared bounds, and escaped-cell sets from codegen |

The copy and scratchpad facade corollaries now expose the same concrete-entry
facts without changing the public theorem shape: checked copy contracts can
project a mapping pair to declared bounds and compatible storage specs, recover
value-trace entries when the value trace is aligned with the copy trace, and in
the scratchpad case project helper targets and copy events against each other.
The phase facade follows the same pattern for the strongest bounded/non-escape
contract: projection value entries directly inherit compatible storage specs
and target bounds, mapped final targets inherit declared bounds, and
entry/read/write/next-live protocol cells directly inherit phase-buffer bounds
and non-escape facts.
The concrete CInstr scalar witnesses now follow the same direct-projection
style: scalar expansion and scalar promotion expose named selected-event
write/read or load/store equality facts instead of requiring callers to unpack
generic value-match predicates.

The public-facing composition surface has now been normalized across the
storage family-compose files.  Copy/scratchpad, inter-array reuse,
conflict-safe reuse, version commit/read, reduction merge, phase projection,
frame preservation, and overlap/private recomputation all keep their lower-level
`view_refinement` theorems where useful, export `public_semantic_refinement`
wrappers, and now expose accepted-certificate `..._certificate_refines`
endpoints backed by the generic pair-certificate refinement predicate in
`StateView.v`.  The current coverage is:
`accepted_bounded_scratchpad_copy_certificate_refines`,
`accepted_declared_copy_protocol_certificate_refines`,
`accepted_bounded_inter_array_reuse_certificate_refines`,
`accepted_bounded_conflict_reuse_certificate_refines`,
`accepted_bounded_version_commit_certificate_refines`,
`accepted_bounded_reduction_merge_certificate_refines`,
`accepted_bounded_phase_projection_certificate_refines`, and
`accepted_bounded_frame_preservation_certificate_refines`, and
`accepted_bounded_overlap_certificate_refines`, in addition to the scalar and
private-storage endpoints listed above.

## Theorem Families

The taxonomy points to three theorem families.

1. Identity/schedule theorems:
   `same_state_relation` on inputs and `State.eq` on outputs.  This is the
   existing affine, tiling, ISS, diamond-without-recomputation, and checked
   annotation route.
2. State-relation theorems:
   target and source executions are related by explicit input and output state
   relations.  Layout remapping, private expansion, contraction, inter-array
   reuse, and double buffering belong here.  `ViewPipeline.v` is the common
   composition spine for the current exploratory variants of this family, and
   `generic_state_view` keeps the endpoint view carrier shared across validator
   functor instances.  `StorageBoundaryView` now also exposes a
   `storage_boundary_transform_contract` bridge into
   `generic_cell_view_transform_contract`, so a finite boundary map can be used
   as the common access-remap/view-refinement object in later pass composition.
3. Trace/instance theorems:
   the target trace projects to the source trace, with roles for internal,
   helper, commit, or merge instances.  Overlap tiling, copy protocols, packing,
   and reduction privatization need this family.  Some of them also need a
   state-relation theorem.

## Mechanization Order

The next mechanization should keep the current validators stable and add new
relations beside them.

1. Make the current `State.eq` route an explicit identity instance of a more
   general `state_view_rel`.  The detailed relation design is in
   `STATE_VIEW_RELATION_DESIGN.md`.
2. Finish the layout/padding story only after proving instruction-level
   simulation for rewritten accesses; access-list remapping alone is not enough.
3. Add a first-class instance-trace witness before attempting overlap, packing,
   or copy protocols.
4. Strengthen private-storage erasure toward scalar expansion.  The current
   branch has the erasure/view theorem shape and a finite
   `ScalarExpansionWitness` for the non-OpenMP core of scalar privatization:
   instance-keyed private-cell selection, private freshness/declaration, event
   consistency, and write-before-read on the expanded trace.  It still does not
   derive those mappings from concrete instruction semantics.
5. Continue strengthening conflict-safe non-injective reuse after the
   state-view relation can express projection from logical values to reused
   physical cells.  The current branch has the finite conflict checker and an
   observer-backed boundary reuse view, plus bounds evidence for the physical
   image of reuse maps.  It still leaves lifetime over-approximation and value
   simulation as semantic obligations.
6. Keep C typing, C integer definedness, no-alias grounding, frame preservation,
   and OpenMP race freedom in a separate boundary contract until the PolIR
   fragment theorem is stable.

## Non-Goals

- Do not weaken `State.eq` globally.
- Do not describe the Python experiments as verified validators.
- Do not treat access lists as a substitute for instruction semantics.
- Do not use Pluto as the organizing principle for storage-changing
  transformations.  Pluto remains useful for schedule-centric cases; storage
  changes need their own witnesses.
