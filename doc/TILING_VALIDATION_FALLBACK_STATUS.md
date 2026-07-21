# Tiling Validation Routes

Status date: 2026-07-21

## Scope

This note defines the observable tiling-validation routes in the integrated
runtime. It also records which layout classes the direct permutable-band
checker recognizes. A successful tiling boundary prints exactly one of
`permutable-band` or `general-fallback`.

## What the Direct Check Establishes

The direct check is PolCert's semantic analogue of Pluto's fully
permutable-band condition. For each selected band component, it asks whether a
source-ordered conflicting instance pair can have the same prefix before the
band and a decreasing value in that component. The checker covers WW, WR, and
RW conflicts and requires every counterexample polyhedron to be certified
empty.

The implementation reuses the proved access-conflict construction and
polyhedral-emptiness kernels from affine validation. It does not construct a
synthetic schedule or call the complete affine-schedule validator. It also does
not reproduce or certify Pluto's band detector, independent-hyperplane search,
or profitability heuristics. The result is a sound semantic property for the
layouts recognized by PolCert's structural bridge.

## Dispatcher Order

`TilingBandDirectRuntime.checked_tiling_schedule_sourceb_first_direct_runtime_validate_route`
tries these proved checks in order:

1. the direct common-band checker for a recognized ordinary strip-mined
   schedule;
2. the direct componentwise checker for a recognized grouped or interleaved
   second-level schedule;
3. the legacy source-first tiling checks;
4. the canonical tiling validator;
5. the general tiling validator.

The first two checks can return `permutable-band`. The last three are all
reported as `general-fallback`. The public label deliberately does not hide a
fallback acceptance under the band name.

| Reported route | Meaning | Candidate used? |
| --- | --- | --- |
| `permutable-band` | A direct semantic band check and its layout-specific reordering theorem established the tiling boundary. | Yes, after the target well-formedness check. |
| `general-fallback` | A proved legacy, canonical, or general tiling validator established the boundary after the direct check returned `false`. | Yes, after the target well-formedness check. |
| `rejected` | No tiling validator accepted the candidate, or a mandatory later consumer rejected the selected route. | No; the enclosing optimizer uses its conservative route behavior. |

`general-fallback` is a successful, proved validation result. It does not mean
that the optimizer returned to the source or trusted Pluto. The theorem
`checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct`
covers both successful labels.

An impure solver alarm is not `false`: it propagates out of the direct check and
does not fall through to a fallback validator.

## Recognized Layouts

The common-band direct path can accept ordinary rectangular tiling and the
tiling leg of diamond and full-diamond pipelines. It additionally requires an
exact strip-mined schedule shape with target-side trailing-zero padding, one
inferred common band and tile recipe, and uniform source schedule arity. The
second-level direct path requires a common
band start and recipe sizes, one program-wide grouped or interleaved layout,
and the supported symmetric trailing-zero equivalence. In each case, the
structural theorem connects a target-order reversal to a decreasing component
of the checked band.

Recognition is intentionally narrower than semantic validity. Source-like
identity schedules and mixed-depth layouts may lack the program-wide slot
mapping required by the direct bridge, so valid instances can report
`general-fallback`. Identity-tiled routes are therefore not classified as
direct merely because they visibly contain tile loops.

For diamond and full-diamond pipelines, the route label describes the tiling
leg from the affine midpoint to the tiled program. The later affine leg is a
separate proof obligation checked by `validate_general`, even when the tiling
leg reported `permutable-band`.

## Current Route Accounting

The direct differential gate contains five comparisons. The direct checker
accepts three and rejects two; of the two direct rejections, the whole-program
checker accepts one and all three compared checkers reject the other. No case
raises an alarm.

The route matrices record the following final dispatcher outcomes:

| Regression | Direct | General fallback | Expected rejection | Notes |
| --- | ---: | ---: | ---: | --- |
| Non-second-level composition matrix | 50 | 34 | 6 | The six rejections are explicit non-innermost vector selections. |
| Second-level manifest | 36 | 17 | 5 | 53 successful validations across direct and fallback routes. |
| Diamond plus second-level consumer matrix | 16 | 0 | 4 | The four rejections are explicit vector-current failures. |

The standalone probes also distinguish the intended boundary: a phase-aligned
ordinary case takes the direct route, a source-like identity case takes the
fallback, and the supported trailing-zero-normalized second-level case takes
the direct route. These counts are route accounting, not a claim that every
future Pluto schedule belongs to one of the direct recognizers.

## Parallel and Vector Consumers

The tiling route is established before checked parallel or vector annotation.
`--multipar` sends every dimension in the finite candidate list constructed for
that route to the checked multi-current configuration; no two-element
truncation remains. The proved route filters the list to certified dimensions
before emitting parallel annotations.

Vector annotation is innermost-only. Pluto-hinted mode considers only the
reported vector hints and does not search non-innermost dimensions. Explicit
`--vector-current d` rejects a selection that is not both certifiable and
structurally innermost. Such an explicit rejection is not a tiling-validator
fallback.

## Maintenance Rules

Future recognizers may broaden the direct route, but they must preserve these
properties:

1. `permutable-band` is emitted only by a theorem chain that checks the band
   property directly.
2. Every accepted non-direct route is reported as `general-fallback`.
3. Regression manifests state the expected route instead of checking success
   alone.
4. Layout classes without a proved structural bridge remain on the fallback.
