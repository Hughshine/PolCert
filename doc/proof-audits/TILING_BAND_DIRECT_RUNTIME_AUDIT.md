# Read-only audit summary: `TilingBandDirectRuntime.v`

## Scope and evidence

- Source: 600 lines.
- Declarations: four fields in `TILING_BAND_DIRECT_RUNTIME_API` and 14 concrete
  implementation declarations (18 rows total in the CSV).
- Proofs: seven concrete proofs; five have inclusive `Proof.`--`Qed.` spans of
  at least 30 lines and are reviewed in
  `/tmp/tiling_band_direct_runtime_long_proofs.md`.
- `/tmp/tiling_band_direct_runtime_declarations.csv` distinguishes API and
  implementation declarations, including duplicate field/implementation names,
  and records callers, dependencies, qualified uses, role, and action.
- The implementation's public runtime roots are used by
  `PolOptBandTiling`, `ParallelPolOpt`, their correctness files, and syntax
  wrappers.  `STilingBandSched.v` directly instantiates the concrete functor and
  also exposes `CoreBandRuntime.Legacy` and
  `checked_tiling_sourceb_complete_direct_band_check`; the driver functors
  ascribe the narrower module type.

This was a read-only audit.  No source change, build, or timing experiment was
performed.

## Runtime route and theorem chain

`checked_tiling_sourceb_first_direct_band_check` first checks the common
source/witness relation, then tries:

1. ordinary common-band strip mining with target-side trailing-zero padding
   and the direct program-wide permutable-band checker;
2. a recognized grouped or interleaved uniform second-level schedule with the
   direct per-statement componentwise permutable-band checker.

`checked_tiling_sourceb_complete_direct_band_check` extends that fail-closed
sequence with:

3. phase-semantic band layouts;
4. scalar-aware layouts;
5. phase-separated ordinary layouts;
6. phase-scalar layouts;
7. semantic-band reconstruction;
8. mixed second-level layouts.

Success from any branch is represented only as `true`; the public wrapper maps
it to `DirectBandAccepted`, and maps complete failure to `Rejected`.  No branch
calls a general affine validator and there is no general-affine fallback.

The correctness chain has matching layers:

- `checked_tiling_sourceb_complete_direct_band_check_sourceb_true` recovers the
  common structural source certificate from any successful route;
- `checked_second_level_direct_band_check_correct` connects second-level shape,
  componentwise permutability, and the layout-specific local bridge;
- `checked_tiling_sourceb_first_direct_band_check_correct` handles the primary
  ordinary and second-level routes;
- `checked_tiling_sourceb_complete_direct_band_check_correct` dispatches all
  eight routes to their already-proved same-context correctness theorems;
- `checked_tiling_sourceb_complete_direct_band_check_outer_correct` transfers
  the result across the outer/tiling representation boundary;
- `checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct`
  proves that an accepted public route yields a source execution with a
  `State.eq`-equivalent final state.

The module is therefore a routing and composition boundary.  The substantive
ordinary, second-level, scalar-aware, phase, semantic, and mixed reversal
arguments live in Core, Mixed, and PhaseScalar.

## Boundary assessment

### API boundary

`TILING_BAND_DIRECT_RUNTIME_API` exposes exactly four concepts: the two-route
result type, its acceptance predicate, the validator, and its semantic theorem.
This is a good driver boundary.  The concrete module intentionally retains more
implementation paths for syntax/debugging clients; those paths should be
treated as compatibility-visible even though the ascribed driver instances hide
them.

The public route carries only `DirectBandAccepted` versus `Rejected`.  It does
not report which of the eight internal variants accepted.  That is sufficient
for correctness and for the current user-visible label (`"permutable-band"`),
but any future diagnostic provenance should be added deliberately to the route
type and its API, not inferred from proof branch order.

### Checker/spec boundary

The runtime does not prove tiling correctness by itself.  Each branch combines:

- the structural source/witness checker from `TilingBoolChecker`;
- a layout/representation recognizer for that variant;
- a direct permutable-band or componentwise permutable-band checker;
- a variant-specific local reversal bridge;
- the common tiling semantic composition theorem.

This division is sound and worth preserving.  In particular, schedule-shape
recognition is not a fallback validator; it explains how target timestamp
coordinates represent the tiled execution on which the checked band property
is interpreted.

## Readability findings

### Route duplication should remain synchronized, not hidden

The eight-branch order appears in the executable dispatcher (`110-139`), the
source-certificate inversion proof (`168-222`), and the complete correctness
proof (`431-469`).  This is deliberate audit surface, but it currently lacks a
single visible route table or synchronized comments.

Add the same four family comments to all three sites:

1. primary ordinary/second-level;
2. phase-semantic/scalar-aware;
3. phase-separated ordinary/phase-scalar;
4. semantic-band/mixed second-level.

Do not replace these proofs with broad automation.  A generic route-fold
abstraction is justified only as a separate executable redesign that also
makes the route list first-class.

### Long proofs are mostly appropriate adapters

The 56-line second-level theorem clearly exposes representation, Boolean band
soundness, local reversal, and semantic composition.  The 81-line first-route
proof necessarily has asymmetric ordinary and second-level branches.  The
68-line outer theorem is the one boundary where context equality,
well-formedness, and semantic transport should remain visible.

These proofs need stage comments, not new Local helpers.  The detailed insertion
points are in the long-proof audit.

### No dead concrete implementation declarations

Every implementation declaration lies in the dependency closure of the public
runtime route or is itself used by the syntax wrapper.  The module-type fields
are all required by driver ascription.  There is no dead proof route to delete
in this file.

## Module-instantiation issue

The current aliases are:

```coq
Module PhaseScalar := TilingBandPhaseScalarValidator PolIRs.
Module Mixed := PhaseScalar.Mixed.
Module Legacy := Mixed.Core.
```

PhaseScalar itself instantiates Mixed only to obtain Core.  Consequently this
runtime reaches the large Core functor through two nested validator facades.
This is a module dependency/build-structure issue, not a semantic defect.

A throwaway dependency-clean prototype can instantiate Core, Mixed, and
PhaseScalar independently, but it must preserve the currently used
`TilingBandDirectRuntime(...).Legacy` path.  It cannot preserve
`PhaseScalar.Mixed` without retaining an equivalent Mixed instantiation, so
that nested path needs an explicit compatibility decision.  Parameterizing the
validators over already-instantiated modules could preserve aliases but is a
larger module-signature redesign.

For any prototype, compare isolated and incremental compile wall time/peak RSS
for Core, Mixed, PhaseScalar, and DirectRuntime, plus the clean full `coqc`
build and existing tests.  Do not use or add `coqchk`.

## Recommended order

1. Add synchronized route-family comments and theorem-stage comments.
2. Keep every runtime theorem name and the sealed API unchanged.
3. Complete the PhaseScalar/Core local-helper cleanup before changing runtime
   module structure.
4. Time a direct-instantiation prototype in a throwaway worktree.
5. Decide explicitly whether `PhaseScalar.Mixed` is an external compatibility
   path; preserve `DirectRuntime.Legacy` in all cases.

This file is not where most proof complexity resides.  Its value is precisely
that it makes the accepted direct routes and the outer semantic boundary
explicit; cleanup should sharpen that map rather than abstract it away.


---

# Long-proof audit: `TilingBandDirectRuntime.v`

Criterion: inclusive `Proof.` through `Qed.` span of at least 30 lines.  The
implementation has seven proofs; five meet the criterion.  The module-type
parameters are contracts, not proof bodies.

## `checked_tiling_sourceb_complete_direct_band_check_sourceb_true` (`162`, proof `168-222`, 55 lines)

**Purpose.** Recovers the common structural source/witness check from success
of any branch in the complete direct dispatcher.

**Proof phases.** `169-174` handles the primary ordinary/second-level checker.
`175-186` handles phase-semantic and scalar-aware routes.  `187-206` handles
phase-separated ordinary and phase-scalar routes.  `207-221` handles the
semantic-band and mixed second-level routes.  Each accepting case delegates to
that route's source inversion theorem; rejected cases continue through the
nested monadic conditionals.

**Assessment.** This is routing inversion, not new tiling theory.  Its branch
shape must mirror `checked_tiling_sourceb_complete_direct_band_check` at
`110-139`, so aggressive tactic compression would make drift harder to audit.
The same route order appears again in the complete correctness proof.

**Low-risk change.** Add comments grouping the four branch families above.  A
larger factoring is worthwhile only if the executable dispatcher is first
represented as a route table/fold with a generic success inversion theorem;
introducing a proof-only abstraction for the current nested `BIND` tree would
not improve readability.

## `checked_second_level_direct_band_check_correct` (`224`, proof `252-307`, 56 lines)

**Purpose.** Connects a recognized grouped/interleaved second-level schedule
and a successful componentwise permutable-band check to semantic equivalence.

**Proof phases.** `256-268` opens the structural source certificate and derives
target/witness alignment.  `269-283` enters the common tiling correctness
theorem and proves composed instructions well formed.  `284-298` turns Boolean
component and schedule checks into their semantic propositions.  `299-306`
uses the generic componentwise-to-reordering theorem and supplies Core's
layout-specific local reversal bridge.

**Assessment.** This is the intended proof architecture in compact form:
representation, checked band property, local layout bridge, generic semantic
composition.  The proof contains no duplicated endpoint reconstruction and is
substantively readable.

**Low-risk change.** Add four stage comments at `256`, `269`, `284`, and `299`.
Keep the theorem and its premises visible; a generic wrapper would hide which
second-level shape and local bridge are actually required.

## `checked_tiling_sourceb_first_direct_band_check_correct` (`309`, proof `329-409`, 81 lines)

**Purpose.** Proves the two primary direct routes: ordinary common-band strip
mining and uniform grouped/interleaved second-level tiling.

**Proof phases.** `332-340` opens the common structural checker and first-route
result.  `341-391` handles ordinary tiling: it inverts schedule/band inference,
enters the common semantic theorem, obtains the strong direct band certificate,
and applies Core's ordinary reordering bridge.  `392-408` handles second-level
tiling by inverting its recognized shape and invoking the preceding theorem.

**Assessment.** The two branches contain different representation evidence and
different local bridges; the asymmetry is real.  The ordinary branch is mostly
composition plumbing, but there is no exact existing high-level theorem whose
checker premises match this dispatcher definition.

**Low-risk change.** Add comments before `332`, `341`, `355`, `377`, and `392`.
Do not extract the second-level branch: it is already a short call.  Revisit the
ordinary block only if Core later exposes a theorem taking precisely
`check_pprog_tiling_schedule_stripminedb` plus the direct band check.

## `checked_tiling_sourceb_complete_direct_band_check_correct` (`411`, proof `431-469`, 39 lines)

**Purpose.** Dispatches successful complete-checker branches to the
corresponding same-context correctness theorem.

**Proof phases.** `434-437` handles the primary route; `438-448` phase-semantic
and scalar-aware; `449-459` phase-separated ordinary and phase-scalar; and
`460-468` semantic-band and mixed second-level.

**Assessment.** This is a proof-shaped mirror of the executable dispatcher.
Every accepting branch immediately calls a proved route theorem.  Its modest
length is useful audit surface, not evidence for a new helper.

**Low-risk change.** Put the same four route-family comments in this proof and
in `checked_tiling_sourceb_complete_direct_band_check_sourceb_true`, using the
same wording and order.  That makes dispatcher/proof drift visible in review.

## `checked_tiling_sourceb_complete_direct_band_check_outer_correct` (`471`, proof `485-552`, 68 lines)

**Purpose.** Moves the same-context tiling correctness result across the public
outer polyhedral representation: it converts the programs, recovers equal
contexts from the source checker, transfers well-formedness, invokes the direct
checker theorem, and converts semantics back.

**Proof phases.** `487-493` names and destructs the converted programs.
`494-511` recovers and applies context/type equality.  `512-526` transfers
affine source well-formedness to tiling instruction well-formedness.
`527-540` transfers general target well-formedness.  `541-551` invokes the
same-context theorem and transports both semantic judgments through
`outer_to_tiling_instance_list_semantics_iff`.

**Assessment.** This is boundary glue rather than band theory, but each step is
needed and the existing Base conversion theorems are used appropriately.  The
two `Forall` assertions are similar in shape but rely on different source
well-formedness theorems, so a one-use generic helper would make the proof less
direct.

**Low-risk change.** Add the five stage comments listed above.  Extract a Local
well-formedness transfer helper only if another outer adapter repeats the same
block.  Keep this theorem as the single visible outer/tiling boundary.

## Priority

1. Add synchronized route-family comments to the dispatcher and its two mirror
   proofs.
2. Add stage comments to the second-level, first-route, and outer adapters.
3. Do not introduce Local helpers in this file yet; none removes a repeated
   semantic argument.
4. Treat any route-table refactor as a separate executable/API change with
   equivalence tests, not as proof cleanup.

The long proofs in this module are not the source of the tiling proof bulk.
They expose the runtime's route order and correctly delegate substantive band
arguments to Core, Mixed, and PhaseScalar.
