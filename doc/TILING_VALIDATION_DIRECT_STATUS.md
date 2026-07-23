# Direct-Only Tiling Validation

Status date: 2026-07-23

## Scope

Every integrated tiling boundary now has two observable outcomes:
`permutable-band` or `rejected`.  A successful boundary is accepted only by
`TilingBandDirectRuntime.checked_tiling_sourceb_complete_direct_band_check`.
The dispatcher has no legacy, canonical, or general tiling-validation
fallback, and its route type has only `DirectBandAccepted` and `Rejected`.

The proof-side optimizer may retain the already verified affine midpoint after
a rejected external candidate.  The extracted CLI reports that route as
`rejected`, returns a nonzero status, and emits no optimized program; it never
counts midpoint recovery as a successful requested tiling.

## Checked Property

The checker establishes a semantic counterpart of Pluto's fully permutable-band
condition.  For every selected component, it rules out a source-ordered WW,
WR, or RW conflict that has the same prefix before the band and decreases in
that component.  The executable check uses the proved guarded dependence
emptiness kernel `BandAffine.validate_two_instrs_under_guards`; it does not call
the whole affine-schedule validator.

The formal result is soundness, not completeness: checker acceptance implies
the componentwise band property and the property implies reordering safety for
the recognized layout.  The implementation does not claim to accept every
semantically valid tiling or to verify Pluto's band detector, hyperplane search,
or profitability decisions.

## Direct Branches

The complete checker tries four fail-closed branches:

1. A common-band bridge for ordinary strip mining and uniform grouped or
   interleaved second-level schedules.  The second-level layout checker accepts
   either symmetric trailing-zero padding or program-wide strict-zero-row
   erasure.  For the latter, all expected schedules share one zero-row mask,
   all imported schedules share one zero-row mask, and removing strict zero
   rows makes each statement's expected and imported schedules identical.
   These conditions preserve cross-statement lexicographic comparisons.
2. A phase-separated ordinary bridge for programs whose statements have
   different band widths after distinct constant phase rows.  Preservation of
   the phase prefix and uniqueness of phase constants reduce every possible
   reversal to one statement; that statement's own inferred band is then
   checked componentwise.
3. Program-wide semantic schedule reconstruction for identity, mixed-width,
   mixed-depth, and source-like layouts.  It preserves global raw tile slots,
   proves globally omitted slots evaluate to zero, and relates compact semantic
   rows to the padded target schedule.
4. A phase-aware mixed second-level bridge for grouped schedules with
   statement-specific bands starting after unique constant phase rows.

Each branch first checks the source/witness relation.  Each accepted branch
connects its checked band components to `pprog_tiling_reordering_safe`, then to
the existing tiling semantic theorem and `State.eq`.

The main correctness theorems are:

- `checked_tiling_sourceb_semantic_band_direct_correct_same_ctxt`
- `phase_separated_ordinary_local_reversal_bridge_wf_with_env_len`
- `check_pprog_phase_separated_ordinary_direct_correct_same_ctxt`
- `check_pprog_mixed_second_level_direct_correct_same_ctxt`
- `check_pinstr_list_second_level_schedule_directb_sound`
- `checked_tiling_sourceb_complete_direct_band_check_correct`
- `checked_tiling_sourceb_complete_direct_band_check_outer_correct`
- `checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct`

## Current Route Accounting

| Regression | Permutable band | Validation fallback | Expected rejection |
| --- | ---: | ---: | ---: |
| Non-second-level composition matrix | 84 | 0 | 6 |
| Second-level manifest | 53 | 0 | 5 |
| Diamond plus second-level consumer matrix | 16 | 0 | 4 |

The non-second-level and second-level accepted sets are disjoint in these
matrices, for 137 direct tiling acceptances.  The diamond-plus-second-level
matrix adds 16 consumer combinations over already supported tiling shapes.
The 15 expected rejections are negative structural cases or explicit
non-innermost vector selections; none is a successful alternate validation
route.

The route manifests require exactly one `permutable-band` report for every
successful tiling candidate and reject any output containing a fallback marker.
The source-level gate additionally forbids fallback constructors, labels, and
calls from the runtime and user-facing tiling paths.

## Boundary Notes

For diamond and full-diamond pipelines, this route validates only the tiling
leg from the affine midpoint to the tiled program.  A later schedule-only
affine leg is a separate transformation and remains checked by
`validate_general`.

Vector annotation is innermost-only.  A rejected non-innermost vector hint or
explicit selection is not a tiling-validation fallback.

## Maintenance Rules

1. `permutable-band` may be emitted only by a theorem chain that checks the
   band property and proves the recognized layout bridge.
2. A direct checker returning `false` must produce `rejected`; it must not
   invoke another tiling validator.
3. Manifests must assert the exact route, not success alone.
4. New layout recognizers require an executable shape check, a true-inversion
   theorem, a reversal bridge, and an end-to-end `State.eq` theorem before they
   enter the dispatcher.
