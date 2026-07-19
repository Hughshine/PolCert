# Tiling Validation Fallback Status

Status date: 2026-07-19

## Scope

This note records why supported tiling routes can report
`[tiling-validation] route=general-fallback`, what that result means, and which
cases should move to the direct permutable-band route.

The observed concentration of fallback cases is a second-level tiling coverage
issue. It does not indicate that the final tiling validation failed.

## Validation Routes

The unified dispatcher tries the following proved checks in order:

1. the ordinary common-band checker;
2. whole-program ordinary-tiling permutability over the composed tiling
   semantics;
3. the second-level componentwise permutable-band checker;
4. the canonical tiling validator;
5. the general tiling validator.

The command-line route labels have these meanings:

| Reported route | Meaning | Optimized tiled result used? |
| --- | --- | --- |
| `permutable-band` | The specialized tiling-permutability layer accepted the boundary through the common-band, whole-program ordinary, or hierarchical second-level mode. This is an umbrella route label, not the name of a single narrow checker. | Yes, after the target well-formedness check passes. |
| `general-fallback` | The specialized tiling-permutability checks did not accept the boundary, but the canonical or general proved tiling validator accepted it. | Yes, after the target well-formedness check passes. |
| `rejected` | The final tiling-bearing pipeline was not adopted, either because no tiling validator accepted the boundary or because a mandatory parallel consumer rejected it. Automatic vector annotation failures are reported separately and retain the verified producer; explicit vector-current failures terminate without reporting a tiling route. | No. The optimizer uses the applicable conservative fallback output when that route defines one. |

Thus `general-fallback` is a successful validation result. It is neither an
unchecked acceptance nor a return to the source program. The route theorem
`checked_tiling_schedule_sourceb_first_runtime_validate_route_correct` covers
both accepted labels. Its general branch invokes
`checked_tiling_validate_poly_correct`.

The current output intentionally combines canonical and general acceptance
under one `general-fallback` label. This public contract answers whether the
specialized band route or a proved fallback accepted the candidate. A deeper
diagnostic mode could distinguish the two fallback validators without changing
the acceptance contract.

## Current Coverage

The current second-level suite manifest contains 20 direct permutable-band
acceptances and 33 explicit fallback acceptances. This is a matrix count, not
33 distinct validator limitations. ISS and parallel, vector, and multipar
consumers repeat the same tiling boundary under different later compilation
routes.

The fallback cases reduce to three structural families. They remain supported
transformations: each case must show a nontrivial optimized result against an
explicit baseline, require the exact fallback route, and reject alarms.

| Family | Current route | Reason for direct-check rejection | Required repair |
| --- | --- | --- | --- |
| Source-like identity plus second-level tiling | `permutable-band` or `general-fallback`, depending on the schedule shape | The direct second-level recognizer accepts some phase-aligned forms, while other source-like schedule forms remain outside its recognition language. | The proved fallback supports the latter; broader direct recognition is optional follow-up. |
| Diamond or full-diamond plus second-level tiling | `general-fallback` | A one-level diamond boundary passes the direct band route. Adding the nested tiling level produces a combined schedule outside the current second-level projection/checking coverage. | Compose the diamond and nested-tiling band projections and prove the resulting direct checker sound. |
| Mixed-depth, multi-statement second-level tiling | `general-fallback` | The direct checker currently requires common second-level recipe sizes and a common band start. Statements at different loop depths need statement-specific bands. | Permit statement-specific band lengths and recipes while checking their cross-statement ordering obligations. |

Ordinary one-level tiling uses either the common-band fast path or the
whole-program ordinary-tiling permutability mode. One-level diamond tiling and
regular phase-aligned second-level tiling also have specialized acceptance
cases. The remaining fallback cases are therefore concentrated in
second-level compositions and heterogeneous statement shapes.

## Final-Gate Checks

The following targeted checks used the current `gifted_curie:/polcert/polopt`
binary:

| Case | Result | Route | Alarm | Optimized output |
| --- | --- | --- | --- | --- |
| Source-like identity, second level, `symbolic-independent-2d.loop` | exit 0 | `general-fallback` | absent | present |
| Mixed-depth second level, `matmul-init.loop` | exit 0 | `general-fallback` | absent | present |
| Diamond plus second level, `diamond-example-inner-batch.loop` | exit 0 | `general-fallback` | absent | present |

The diamond diagnostic further reported that the canonical checker rejected
the boundary while the general checked tiling validator accepted it. This
confirms that the general fallback is exercised and works for that case.

The complete second-level regression suite covers 20 specialized acceptances,
33 explicit fallback cases, a 20-case diamond/current/strict matrix, and
focused rejection checks. The diamond matrix now separates 16 accepted
parallel/hinted compositions from four explicit vector-current hard failures;
the latter report no tiling route. The manifest gate requires every fallback
case to provide an explicit baseline comparison; the mixed-depth case compares
its 256/32 nested output against ordinary tiling.
A prior isolated full-gate run took `954.751s`; budget roughly 16 minutes for
this suite on the documented container before accounting for concurrent load.

The separate Pluto compatibility matrix passed all 133 checks in about five
minutes in `gifted_curie`. A dedicated 90-case one-level route-discipline matrix then ran
ordinary, identity-tiled, diamond, and full-diamond producers; ISS and non-ISS
routes; uniform and mixed-depth programs; and sequential, hinted, strict,
multipar, parallel-current, and vector-current consumers. Under the
innermost-only vector contract, 84 compositions complete and emit exactly one
`permutable-band` report. Six explicit vector-current selections are expected
hard failures because the selected loop is not a certifiable innermost vector
loop; they emit vector rejection telemetry and no tiling route. Automatic
missing or rejected hints retain the verified producer. No case uses
`general-fallback`.

This matrix checks completion or expected explicit-vector rejection, the
unique validation-route report for completed cases, and alarm discipline. It
does not claim that every flag has a distinct optimization effect in every
Cartesian-product case. Separate compatibility,
parallel-current, vector-current, and diamond suites provide representative
effect assertions for those features.

This is a claim about the current supported matrix, not every schedule a future
Pluto version might produce. A future valid schedule outside the specialized
recognizers may still succeed through the proved fallback, with
`general-fallback` reported explicitly.

## Follow-Up Acceptance Criteria

Optional direct-recognition work may:

1. expose the failed direct-check stage or predicate in diagnostic mode;
2. move additional source-like identity second-level shapes to
   `permutable-band`;
3. move diamond and full-diamond second-level combinations to
   `permutable-band`;
4. move supported mixed-depth second-level cases to `permutable-band`;
5. update the regression manifests to require the direct route and reject any
   fallback report for those cases;
6. retain the proved fallback validators for valid schedules outside the
   direct checker's intended recognition language.

The target is not to delete fallback. The target is to make direct
permutable-band validation the normal route for every advertised Pluto tiling
family, with fallback reserved for structurally valid schedules beyond that
direct coverage.
