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
The first implementation step is `StateView.v`, which packages endpoint
relations as views and wraps the existing affine/general validators as
`same_state_view -> identity_view` refinements.  It also exposes a small
relation-inclusion algebra (`view_included_refl`, `view_included_trans`, and
`compose_view_monotone`) so storage validators can compose endpoint views
without unfolding the underlying state relations.  The current layout skeleton
also exposes `related_cells_view` and a `layout_view`-level theorem, so the
layout prototype no longer bypasses the view endpoint.  `StateObservation.v`
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
public and private boundary values match for each aligned boundary pair.
Related skeletons include
`TransformContract.v`, `StateView.v`, `ViewPipeline.v`,
`StorageWitness.v`, `SourceNoAliasWitness.v`,
`FramePreservationWitness.v`, `FrameValueWitness.v`,
`FramePreservationValidator.v`,
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
`ReuseStateView.v`, `StorageBoundaryView.v`, `ReuseConflictValidator.v`,
`InstanceProjectionWitness.v`,
`InstanceProjectionValidator.v`, `OverlapClosureWitness.v`,
`OverlapTilingValidator.v`,
`VersionCommitWitness.v`, `VersionCommitValueWitness.v`,
`VersionCommitValidator.v`, `ReductionMergeWitness.v`,
`ReductionMergeValueWitness.v`, `ReductionMergeValidator.v`,
`PhaseSeparationWitness.v`, `PhaseValueWitness.v`,
`PhaseProjectionWitness.v`,
`PhaseSeparationValidator.v`, and
`CStateObservation.v`.
`StateView.v` now uses a top-level `generic_state_view` carrier so independently
instantiated validators can share one facade-level view type instead of
exporting incompatible functor-local records.  `ViewPipeline.v` factors out the
repeated composition pattern shared by most storage validators: the existing
general validator proves `before -> source_view`, while the feature-specific
pass supplies finite witness obligations plus an explicit semantic
`view_refinement` from `source_view` to the storage-changing target.
`TransformContract.checked_relational_transform_family_pair_compose` and
`StateView.checked_view_transform_family_pair_compose` are the current generic
two-pass composition hooks: two checked passes compose by composing their input
and output relations/views, so feature checkers do not need bespoke end-to-end
theorems for every pass ordering.
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
non-escape.  `CInstrScalarExpansionWitness.v` is the first concrete
instruction-facing bridge: paired CInstr assignment steps can justify one
expansion write/value event, and paired scalar access evaluations can justify
one expansion read/value event.  The bridge also exposes the underlying
`CInstr.semantics` steps for writes and gives read/write singleton value-flow
lemmas that work from an arbitrary current private-value map, which is the
shape needed for later pass-level trace composition.  It now also contains an
ordered trace witness: a list of CInstr-derived scalar-expansion reads and
writes threads the current private-value map through schedule order and proves
the generic scalar-expansion value-flow obligation, while separately exposing
that the trace events are mapped by the declared expansion entries.
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
safe.  The CInstr bridge uses this to offer a smaller static-core theorem where
declared entries, hidden cells, and freshness are checked, while event mapping
and use-def come from the ordered CInstr trace.
The same static-trace route now has a bounded variant that adds private bounds,
source/private storage compatibility, and non-escape checks before returning
the bounded scalar privatization obligation package and the same public-view
refinement conclusion.  The bridge now also provides public-refinement-only
facade theorems for both the static and generic CInstr trace routes.  These
theorems deliberately hide the scalar-expansion contract records from the
composition-facing conclusion, so the endpoint remains the intuitive
public-view semantic refinement.
`SourceNoAliasWitness.v` makes the front-end memory abstraction explicit: each
logical source object has a duplicate-free finite footprint, object ids are
duplicate-free, different footprints are pairwise disjoint, and a finite list
of source read/write cells can be checked against those declared footprints.
This remains a precondition witness rather than a transformation theorem.
`FramePreservationWitness.v` adds the generic contextual boundary condition:
fragment writes must be contained in an allowed-write set, and that allowed set
must be disjoint from frame cells owned by the surrounding context.
`FrameValueWitness.v` adds the corresponding finite value snapshot layer:
each context-frame cell is aligned with a before/after value pair and those
values must match.
`FramePreservationValidator.v` packages that side condition with the common
source-view theorem shape, so feature-specific storage views can carry a frame
contract without changing their final-state relation.
`PaddingLayoutWitness.v` adds the finite allocation side of layout/padding:
source cells map functionally to target cells, target cells are injective and
allocated, and padding cells are duplicate-free, allocated, and outside the
represented target image.  `StorageBoundsWitness.v` adds the structured
in-bounds side: declared array extents are well formed, finite physical cells
can be checked against those extents, and padding/layout validators can require
all allocated physical cells to be within declared bounds.  `LayoutValueWitness.v` adds the boundary value side:
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
scalar value.  `CInstrScalarPromotionWitness.v` now connects this value-flow
layer to concrete CInstr semantics: load/read/write/store/global-write events
can be derived from CInstr access, expression-evaluation, and assignment
steps, and an ordered CInstr-derived trace proves the generic scalar-promotion
value-flow obligation.  `CInstrScalarPromotionValidatorBridge.v` connects that
CInstr trace evidence to the existing scalar-promotion view wrappers, including
the compatible and bounded/non-escape variants, without changing their
public-view refinement conclusion.  It also exposes public-refinement-only
facade theorems, so downstream composition can consume only the semantic
endpoint while the trace, compatibility, bounds, separation, and non-escape
proofs remain internal obligations.  `ScalarPromotionValidator.v` composes the
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
value.  `CopyProtocolValidator.v` packages both the bookkeeping-only and
value-flow variants into composable `view_refinement` theorems under an
explicit instruction-level semantic refinement.
`ScratchpadCopyValidator.checked_scratchpad_copy_full_view_correct` lifts the
copy remapping and value-flow witnesses to the scratchpad/packing composition
layer together with instance projection, copy-out exact cover, helper-instance
roles, and local-buffer separation.  The bounded declared variant additionally
requires every mapping-local cell to be declared as a local buffer cell and
checks those declared local cells against array bounds.  The fully declared
variant checks both sides of the mapping and can derive bounds facts for both
the mapped public cells and mapped local cells.
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
physical boundary value must equal the logical value it represents.
`ReuseConflictWitness.v` also checks boundary coverage: every source-observable
live-out selected for final projection must be present in the reuse map.  It
now also exposes the physical image of a reuse map, so contraction-style
validators can connect every actually reused physical cell to declared storage
bounds rather than checking an unrelated cell list.
`StorageCompatibilityWitness.v` adds a finite size/alignment compatibility
checker for logical-to-physical storage maps.  This captures the explicit
storage-class side condition needed by contraction, inter-array reuse, packing,
and scratch/local-buffer reuse without pretending that the specs have already
been derived from C types.
`InterArrayReuseWitness.v` packages the inter-array reuse case without adding
a new primitive: it combines live-interval conflict cover, conflict-safe reuse,
and storage compatibility.  Its derived facts say that mapped live-overlapping
logical cells have distinct physical cells, and therefore two distinct logical
cells that share one physical cell cannot overlap in their live intervals.
`InterArrayReuseValidator.v` gives that composed finite witness the same
`view_refinement` endpoint theorem shape as the other storage features.  Its
bounded variant additionally requires the shared physical image of the reuse
map to lie inside declared buffer bounds, while still leaving the concrete
boundary projection as the supplied output view.
`ReuseStateView.v` turns a boundary reuse map into an observer-backed reuse
projection view, and now also exposes a `cell_view` for a declared live-out
boundary whose target-public cells are exactly the mapped image.
`StorageBoundaryView.v` is the first shared endpoint wrapper for storage-backed
boundary maps: it combines `check_reuse_boundaryb_sound`,
`check_storage_compatibilityb_sound`, and the observer-backed boundary view into
one theorem, so layout, phase projection, reuse/contraction, and copy-out style
passes can share the same final-observation discipline when their live-outs are
represented by a finite logical-to-physical map.
`ReuseConflictValidator.v` composes the finite conflict
checker, the optional live-range cover checker, the optional storage
compatibility checker, and the value witness under the remaining semantic
refinement shape.  Its bounded variants compose those obligations with
`StorageBoundsWitness` and derive that every mapped physical target returned by
`reuse_lookup` is within the declared physical bounds.
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
with `StorageBoundsWitness`, so internal recomputation writes can be checked
within declared tile-private buffer bounds and commit writes within declared
public-output bounds.
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
fully bounded read/commit route now checks that every read-selected produced
version is within its declared version-array bounds as well as every committed
version.
`ReductionMergeWitness.v` starts the reduction-privatization route by checking
chunk exact cover, private accumulator uniqueness, and merge-order cover;
it also exposes the exact-cover consequences as named lemmas for later
semantic proofs.
`ReductionMergeValueWitness.v` checks the narrower value-flow side: merge-order
cells are looked up in supplied accumulator values and folded with a supplied
merge operator to the claimed final value.  `ReductionMergeValidator.v`
composes both variants while keeping the reduction algebra law explicit.  Its
bounded non-escape variant also threads `StorageBoundsWitness` through private
accumulators, so every private accumulator consumed by the merge can be shown
to lie within declared accumulator-buffer extents.
`PhaseSeparationWitness.v` starts the double-buffering route by checking phase
read visibility, write/live disjointness, and next-live coverage;
`PhaseValueWitness.v` adds phase snapshot value flow: reads have entry values,
and every next-live value is either written in the phase or inherited from the
entry snapshot.  `PhaseProjectionWitness.v` checks the final-boundary projection
from source logical live-outs to the final phase-live physical cells, with an
optional value-equality layer for those projected cells.  It also exposes the
projection map as a target-to-source `cell_relation` and names the exact-cover
consequences used by later view proofs.
`PhaseSeparationValidator.v` composes these variants while keeping the
phase/swap semantic meaning explicit.  Its bounded projection variant also
connects final phase-live target cells to declared buffer bounds and derives
that every mapped target cell exposed by the projection relation is in bounds.
The bounded phase-protocol variant separately exposes the finite image of all
entry-live, read, write, and next-live cells used by the phase trace, so the
protocol itself can be checked against declared buffer bounds before any final
projection is considered.
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
| P-1 no-alias memory abstraction | `SourceNoAliasWitness.check_source_no_aliasb_sound`; `SourceNoAliasWitness.check_source_no_alias_accessb_sound`; `SourceNoAliasWitness.check_source_no_alias_access_boundedb_sound`; `SourceNoAliasWitness.source_access_cell_covered`; `SourceNoAliasWitness.source_access_cell_within_bounds` | object ids and finite footprints are duplicate-free; footprints are pairwise disjoint; finite source access cells can be checked to lie inside the declared footprint for their logical object; footprint cells can be checked against declared array bounds, so covered source access cells inherit in-bounds facts | deriving the finite access cells and proving they over-approximate real C accesses |
| P0/P1 projection and roles | `InstanceProjectionWitness.check_instance_projectionb_sound` | projected target instances are in the source domain; commit-role instances exactly cover live-outs | deriving projected target sets from concrete codegen |
| P1 local dependence closure | `OverlapClosureWitness.check_overlap_closureb_sound`; `OverlapClosureWitness.check_overlap_ordered_closureb_sound`; `OverlapClosureWitness.overlap_closure_dependency_consumer_in_targets`; `OverlapClosureWitness.overlap_closure_dependency_available`; `OverlapClosureWitness.overlap_ordered_closure_dependency_ordered` | every finite tile dependency consumer belongs to the tile's projected target sources; every dependency producer is supplied by a tile live-in or a projected computation in the same tile; in the ordered variant, tile-produced dependencies precede their consumers | deriving dependencies and trace order from concrete schedule/access semantics |
| P2 access-map refinement | `LayoutWitness.check_pprog_declared_layout_access_remapb_sound`; `LayoutRemapValidator.checked_declared_layout_remap_correct`; `LayoutRemapValidator.checked_declared_layout_remap_relational_correct`; `LayoutRemapValidator.checked_declared_layout_remap_view_correct` | same-instance access-list remap through a single declared-layout interface covering same-index array rename, index permutation such as transpose, and affine-composed index rewrites such as linearization; the declared-layout access witness can now be packaged under the common source-view composition theorem in observation, relational, and view forms | instruction-level value simulation for rewritten accesses; deriving layout declarations from generated code |
| P2 plus padding | `PaddingLayoutWitness.check_padding_layoutb_sound`; `PaddingLayoutWitness.padding_layout_boundary_obligations`; `StorageBoundsWitness.check_storage_boundsb_sound`; `LayoutWitness.check_pprog_declared_layout_access_remapb_sound`; compatibility hooks for the older rename/permutation/affine checkers; `LayoutValueWitness.check_layout_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `PaddingLayoutValidator.checked_padding_layout_declared_access_bounds_compatible_value_view_correct` | target image is injective and allocated; padding is duplicate-free, allocated, and outside the image; the finite source-to-target layout map yields shared storage-boundary obligations for endpoint views; allocated physical cells can be checked against declared array extents; target/source access functions can be checked under one declared-layout witness; mapped source/target boundary values match; mapped physical layout cells can be required size/alignment-compatible with represented logical cells | deriving value entries, storage specs, and declared bounds from concrete semantics and deriving layout declarations from generated code |
| P3 fresh private storage | `PrivateStorageWitness.check_private_separationb_sound`; private use-def checkers; `PrivateStorageWitness.check_private_trace_cells_declaredb_sound`; `PrivateStorageWitness.check_private_access_instances_declaredb_sound`; `ScalarExpansionWitness.check_scalar_expansionb_sound`; `ScalarExpansionWitness.scalar_expansion_events_same_key_same_private`; `ScalarExpansionValueWitness.check_scalar_expansion_value_traceb_sound`; `CInstrScalarExpansionWitness.cassign_scalar_expansion_write_singleton_value_flow`; `CInstrScalarExpansionWitness.caccess_scalar_expansion_read_singleton_value_flow_from_current`; `ScalarExpansionValidator.checked_value_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_bounded_value_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_bounded_pure_scalar_privatization_correct`; `ScalarExpansionValidator.checked_scalar_expansion_view_correct`; `ScalarExpansionValidator.checked_scalar_expansion_bounded_compatible_non_escape_view_correct`; `ScalarExpansionValidator.scalar_expansion_view_event_source_cell_hidden`; `ScalarExpansionValidator.scalar_expansion_event_private_cell_within_bounds`; `ScalarExpansionValidator.scalar_expansion_event_private_cell_not_escaped`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateBoundaryWitness.check_private_boundaryb_sound`; `PrivateBoundaryWitness.check_private_boundary_private_uniqueb_sound`; `PrivateBoundaryWitness.check_private_boundary_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `PrivateStorageValidator.checked_bounded_declared_boundary_private_unique_compatible_non_escape_value_expansion_view_correct`; `PrivateStorageValidator.checked_access_bounded_declared_local_private_expansion_view_correct`; `PrivateStorageValidator.private_declared_trace_cell_within_bounds`; `PrivateStorageValidator.private_access_instantiated_trace_cell_within_bounds` | private cells are duplicate-free and disjoint from public/frame cells; private reads have prior writes; concrete private trace cells are declared private cells; access-function private traces can be instantiated over a finite point set and each instantiated cell must be declared private; scalar expansion entries map each `(source instance, source scalar cell)` key to a unique declared private cell, all expansion events use that declared mapping consistently, the source scalar cells being replaced must also be hidden from the public endpoint view for the pure no-copy-out case, the resulting private trace is write-before-read, scalar expansion value traces check that private writes store the source logical value and private reads observe a value equal to the represented source read, CInstr assignment/access semantic steps can be connected to those write/read value events, and the checked pure-scalar-privatization wrappers state the public-view refinement theorem directly; scalar expansion can now also compose private bounds, source/private storage compatibility, non-escape, and value-flow evidence in one top theorem, yielding per-event source-hidden, private in-bounds, and non-escaping private-cell corollaries; declared private cells can be checked against array bounds; required live-ins/live-outs have boundary pairs; live-out public commits are unique; boundary private cells can be required unique; boundary public/private values match; boundary public/private cells can be required size/alignment-compatible; non-escape, declared trace coverage, finite access instantiation, bounds, uniqueness, value evidence, and compatibility can be composed in private-erasure theorem shapes | deriving full instruction traces, finite point sets, boundary value entries, escaped-cell sets, declared bounds, storage specs, and expansion mappings from concrete expression and type semantics |
| P4 copy protocol | `CopyProtocolWitness.check_copy_protocol_wfb_sound`; `CopyCommitWitness.check_copy_commit_coverb_sound`; `CopyCommitWitness.copy_commit_boundary_obligations`; `CopyInstanceWitness.check_copy_instance_traceb_sound`; `CopyMappingWitness.check_copy_mappingb_sound`; `CopyMappingWitness.check_copy_mapping_local_declarationb_sound`; `CopyMappingWitness.check_copy_mapping_declarationb_sound`; `CopyProtocolValueWitness.check_copy_value_traceb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `CopyProtocolValidator.checked_copy_protocol_commit_mapping_value_view_correct`; `CopyProtocolValidator.checked_copy_protocol_commit_mapping_bounded_value_view_correct`; `CopyProtocolValidator.checked_copy_protocol_declared_bounded_compatible_commit_mapping_value_view_correct`; `CopyProtocolValidator.copy_protocol_committed_target_within_bounds`; `CopyProtocolValidator.copy_protocol_mapping_public_within_bounds`; `CopyProtocolValidator.copy_protocol_mapping_local_within_bounds` | local reads are covered by prior local definitions; copy-out targets are duplicate-free and can exact-cover expected observable targets; committed public copy-out targets yield an identity storage-boundary map for shared endpoint views; copy protocol events align with internal/commit projected helper instances; public-to-local remap is injective and used consistently by copy/local events; mapping-local cells can be required to belong to the declared local-buffer set; the stronger declaration checker also requires mapping-public cells to belong to the declared public set; copy/local/commit value flow is consistent; generic copy protocol can package commit exact cover, remapping, value flow, declared public/local mapping coverage, public/local storage compatibility, and declared bounds for commit targets plus mapped public/local cells in one view theorem; committed targets inherit the expected-target bounds through exact cover, and mapped public/local cells inherit their declared bounds | deriving the trace, value trace, helper-instance list, storage specs, and declared commit/public/local bounds from concrete instruction semantics |
| P4 scratchpad/packing composition | `ScratchpadCopyValidator.checked_scratchpad_copy_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_instance_commit_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_bounded_fully_declared_compatible_full_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_bounded_fully_declared_compatible_non_escape_full_view_correct`; derived facts such as `ScratchpadCopyValidator.scratchpad_copy_mapping_public_within_bounds`, `ScratchpadCopyValidator.scratchpad_copy_mapping_local_within_declared_bounds`, `ScratchpadCopyValidator.scratchpad_copy_mapping_local_not_public`, `ScratchpadCopyValidator.scratchpad_copy_local_cell_not_escaped`, and `ScratchpadCopyValidator.scratchpad_copy_mapping_local_not_escaped` | projection, copy protocol, optional copy-out exact cover, optional copy-instance role alignment, public-to-local remapping, declared public/local coverage for mapping cells, copy value flow, local-buffer separation, public/local storage compatibility, declared public/local bounds, and optional local-buffer non-escape compose into `view_refinement`; mapping-public and mapping-local cells lie within their declared bounds, mapping-local cells are separated from public cells, every declared local-buffer cell can be required not to escape the fragment, and mapping-local cells inherit that non-escape fact | deriving the trace, value trace, helper-instance list, storage specs, declared bounds, escaped-cell sets, and full copy-mediated semantic simulation |
| P5 scalar simulation | `ScalarPromotionWitness.check_scalar_promotionb_sound`; `ScalarPromotionValueWitness.check_scalar_value_traceb_sound`; `ScalarPromotionValidator.checked_scalar_promotion_compatible_value_view_correct`; `ScalarPromotionValidator.checked_scalar_promotion_bounded_compatible_non_escape_value_view_correct`; derived facts `ScalarPromotionValidator.scalar_promotion_source_cell_within_bounds`, `ScalarPromotionValidator.scalar_promotion_scalar_cell_within_bounds`, and `ScalarPromotionValidator.scalar_promotion_scalar_cell_not_escaped` | load-before-use, no bypassing source write, live-out store-back; scalar value-flow consistency; promoted scalar/register storage can be required compatible with the source cell; source and promoted scalar cells can be checked against declared storage bounds; promoted scalar/register storage can be required not to escape the fragment | deriving the value trace, storage specs, declared source/scalar bounds, and escaped-cell sets from concrete expression/type semantics |
| P6 conflict-safe reuse | `LifetimeConflictWitness.check_live_conflictb_sound`; `ReuseConflictWitness.check_conflict_safe_reuseb_sound`; `ReuseConflictWitness.reuse_lookup_target_in_targets`; `ReuseConflictWitness.conflict_safe_reuse_boundary_obligations`; `ReuseValueWitness.check_reuse_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `StorageBoundaryView.checked_storage_boundary_refinement_correct`; `ReuseConflictValidator.checked_bounded_compatible_live_conflict_reuse_value_view_correct`; `ReuseConflictValidator.bounded_compatible_live_reuse_mapping_target_within_bounds`; `InterArrayReuseWitness.check_inter_array_reuseb_sound`; `InterArrayReuseWitness.inter_array_reuse_boundary_obligations`; `InterArrayReuseValidator.checked_bounded_inter_array_reuse_view_correct`; `InterArrayReuseValidator.bounded_inter_array_reuse_mapping_target_within_bounds`; `InterArrayReuseValidator.bounded_inter_array_overlap_mapped_distinct`; `InterArrayReuseValidator.bounded_inter_array_same_physical_not_live_overlap` | explicit live intervals cover all overlap conflicts; conflicting logical values do not map to the same physical cell; every mapped physical target is in the reuse-map image; every source in a conflict-safe reuse map, including the inter-array facade, is covered as a reusable boundary footprint; boundary physical values equal represented logical values; mapped logical/physical cells have compatible size/alignment specs; mapped physical cells can be checked against declared bounds; a finite boundary map can be turned into a shared observer-backed endpoint view; live conflicts, reuse, compatibility, bounds, and boundary values can be packaged in one contraction-facing view theorem; inter-array sharing is the composed case where one physical cell cannot represent two simultaneously live logical cells, and its shared buffer cells can also be bounded; from the bounded inter-array contract, overlapping live intervals map to distinct physical cells, so same-physical sharing implies no live overlap | deriving live intervals, storage specs, declared physical bounds, and boundary values from schedule/access/type semantics |
| P7 version selection and commit | `VersionCommitWitness.check_version_commitb_sound`; derived facts such as `VersionCommitWitness.version_commit_liveout_selected`, `VersionCommitWitness.version_commit_selected_source_liveout`, and `VersionCommitWitness.version_commit_boundary_obligations`; `VersionReadWitness.version_read_selected_version_in_produced_versions`; `VersionCommitValueWitness.check_version_valueb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `VersionCommitValidator.checked_version_commit_bounded_compatible_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_bounded_compatible_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_fully_bounded_compatible_value_view_correct`; `VersionCommitValidator.checked_version_commit_read_fully_bounded_compatible_non_escape_value_view_correct`; `VersionCommitValidator.version_commit_selected_version_within_bounds`; `VersionCommitValidator.version_read_selected_version_within_produced_bounds`; `VersionCommitValidator.version_produced_version_not_escaped`; `VersionCommitValidator.version_read_selected_version_not_escaped` | selected source live-outs and selected target versions are duplicate-free and exactly covered; every live-out has a selected version; selected relation edges point back to live-outs; the selected mapping sources are covered as a reusable boundary-view footprint; read-selection entries select produced versions for their expected dynamic producers; selected-version value evidence matches the mapping; selected physical versions can be required storage-compatible with represented source live-outs; committed selected versions and internal read-selected produced versions can both be checked against declared version-array bounds, with per-cell derived bounds facts; produced internal version cells can additionally be required not to escape, and target reads that select produced versions inherit that non-escape fact | deriving selected-version values, produced-version read witnesses, storage specs, declared version-array bounds, escaped-cell sets, and concrete write/type semantics |
| P8 reduction merge | `ReductionMergeWitness.check_reduction_mergeb_sound`; `ReductionMergeValueWitness.check_reduction_value_mergeb_sound`; `ReductionAlgebraWitness.check_reduction_*_lawb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `ReductionMergeValidator.checked_reduction_merge_commutative_bounded_compatible_non_escape_value_view_correct`; `ReductionMergeValidator.reduction_private_accumulator_within_bounds`; `ReductionMergeValidator.reduction_merged_accumulator_within_bounds`; `ReductionMergeValidator.reduction_private_accumulator_not_escaped`; `ReductionMergeValidator.reduction_merged_accumulator_not_escaped` | chunks cover the reduction domain; private accumulators and merge order are well formed; merge-order accumulator values fold to the claimed final value; a finite carrier can witness closure, associativity, commutativity, and identity laws; private accumulators can be required size/alignment-compatible with the public reduction cell; private accumulators can be required non-escaping and within declared accumulator-buffer bounds; every accumulator in the merge order inherits the same bounds and non-escape facts; bookkeeping, value, algebra, compatibility, bounds, and non-escape evidence can be packaged in one view theorem | deriving accumulator values/storage specs/declared bounds and connecting finite-carrier laws to concrete C/FP semantics |
| P9 phase separation | `PhaseSeparationWitness.check_phase_protocolb_sound`; `PhaseSeparationWitness.phase_protocol_cells`; `PhaseValueWitness.check_phase_value_protocolb_sound`; `PhaseValueWitness.check_phase_value_protocolb_final_snapshot`; `PhaseProjectionWitness.check_phase_projectionb_sound`; `PhaseProjectionWitness.check_phase_projection_valueb_sound`; `PhaseProjectionWitness.phase_projection_sources_covered`; `PhaseProjectionWitness.phase_projection_boundary_obligations`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `StorageBoundaryView.checked_storage_boundary_refinement_correct`; `PhaseSeparationValidator.checked_phase_separation_bounded_view_correct`; `PhaseSeparationValidator.checked_phase_separation_bounded_non_escape_view_correct`; `PhaseSeparationValidator.checked_phase_projection_bounded_compatible_value_view_correct`; `PhaseSeparationValidator.phase_protocol_entry_live_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_read_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_write_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_next_live_cell_within_bounds`; `PhaseSeparationValidator.phase_protocol_entry_live_cell_not_escaped`; `PhaseSeparationValidator.phase_protocol_read_cell_not_escaped`; `PhaseSeparationValidator.phase_protocol_write_cell_not_escaped`; `PhaseSeparationValidator.phase_protocol_next_live_cell_not_escaped`; `PhaseSeparationValidator.phase_projection_mapped_target_within_bounds` | reads are visible, writes do not overwrite live cells, next-live cells are covered, entry/read/write/next-live protocol cells can be required to lie within declared buffer bounds, and for fragment-private ping-pong/local phase protocols those same protocol cells can be required not to escape; next-live values come from phase writes or entry-live values, the checked value protocol yields a final snapshot matching final-live cells, final source live-outs are exactly projected to final phase-live cells, projected boundary values match, projected final phase cells can be required size/alignment-compatible with represented live-outs, projected final phase cells can also be checked against declared bounds, and the final projection now yields the shared reusable boundary-view obligations used by storage-backed endpoint relations | deriving the phase/swap projection, storage specs, declared buffer bounds, escaped-cell sets, and target code phase arithmetic |
| P10 frame preservation | `FramePreservationWitness.check_frame_preservationb_sound`; per-cell corollaries such as `FramePreservationWitness.frame_preservation_write_not_frame`; `FrameValueWitness.check_frame_valueb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `FramePreservationValidator.checked_frame_preservation_value_view_correct`; `FramePreservationValidator.checked_frame_preservation_bounded_value_view_correct`; `FramePreservationValidator.frame_preservation_frame_cell_value_preserved`; `FramePreservationValidator.frame_preservation_write_within_allowed_bounds`; `FramePreservationValidator.frame_preservation_frame_cell_within_bounds` | writes are included in the allowed-write set; allowed writes are disjoint from frame cells; each fragment write is therefore outside the context frame; aligned frame before/after values are equal for every listed frame cell; allowed-write cells and context-frame cells can be checked against declared array bounds; fragment writes inherit the allowed-write bounds; the side condition can be packaged with the common source-view theorem shape | deriving the write set, declared bounds, and frame snapshots from concrete instruction semantics |
| overlap-specific composition | `OverlapTilingValidator.checked_overlap_*_view_correct`; `OverlapStorageWitness.check_overlap_storageb_sound`; `StorageBoundsWitness.check_storage_boundsb_sound`; `PrivateStorageWitness.check_private_non_escapeb_sound`; `OverlapTilingValidator.checked_overlap_private_ordered_closure_bounded_compatible_value_storage_view_correct`; `OverlapTilingValidator.checked_overlap_private_ordered_closure_bounded_compatible_non_escape_value_storage_view_correct`; `OverlapTilingValidator.overlap_internal_write_within_private_bounds`; `OverlapTilingValidator.overlap_commit_write_within_commit_bounds`; `OverlapTilingValidator.overlap_internal_write_not_escaped` | duplicated/internal instances project to source instances and commits are unique; optional tile-local closure and private separation; internal writes target tile-private cells and commit writes target public commit cells; private/commit write-cell regions can be checked against declared bounds, role-specific writes inherit the corresponding bounds fact, and tile-private internal writes can be required not to escape the fragment | recomputed-value equivalence and deriving concrete target write cells, storage specs, declared bounds, and escaped-cell sets from codegen |

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
