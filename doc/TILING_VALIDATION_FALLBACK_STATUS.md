# Tiling Validation Fallback Status

Status date: 2026-07-19

## Scope

This note records what `[tiling-validation] route=general-fallback` means and
how the direct permutable-band route covers the current supported tiling
matrix. The fallback remains available for valid future schedules outside the
specialized recognizers; no known successful case in the current second-level
matrix requires it.

## Validation Routes

The unified dispatcher tries the following proved checks in order:

1. the ordinary common-band checker;
2. whole-program ordinary-tiling permutability over the composed tiling
   semantics;
3. the second-level componentwise permutable-band checker;
4. for a structurally recognized second-level target, whole-program
   permutability over the composed tiling semantics;
5. for a structurally recognized source-like class of second-level schedules,
   whole-program permutability over the composed tiling semantics;
6. the canonical tiling validator;
7. the general tiling validator.

The command-line route labels have these meanings:

| Reported route | Meaning | Optimized tiled result used? |
| --- | --- | --- |
| `permutable-band` | The specialized tiling-permutability layer accepted the boundary through the common-band, whole-program ordinary, hierarchical second-level, structural second-level whole-program, or source-like second-level whole-program mode. This is an umbrella route label, not the name of a single narrow checker. | Yes, after the target well-formedness check passes. |
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

The current second-level suite manifest contains 53 direct permutable-band
acceptances and no known fallback acceptance. ISS and parallel, vector, and
multipar consumers repeat the same tiling boundary under different later
compilation routes.

Ordinary one-level tiling uses either the common-band fast path or the
whole-program ordinary-tiling permutability mode. One-level diamond tiling and
regular phase-aligned second-level tiling use their specialized checks.
The statementwise second-level recognizer parses each recipe, independently
infers its source band, and checks either the grouped child/root target layout
or the canonical interleaved root/child layout. It therefore covers both
mixed-depth programs with statement-specific band lengths and diamond or
full-diamond targets whose added iterators are interleaved. The dispatcher then
checks permutability of the complete composed schedule, including cross-
statement ordering. This recognizes semantic structure rather than command-
line provenance.
The source-like class uses a guarded whole-program permutability check; current
identity producers exercise this class, but the selector does not inspect CLI
flags.
For every statement, the validator parses the second-level recipe, requires a
strict zero root row, and checks that deleting strict zero rows makes the
recipe roots equal the source schedule. It then checks the complete composed
schedule.

## Final-Gate Checks

The following targeted checks used the current `gifted_curie:/polcert/polopt`
binary:

| Case | Result | Route | Alarm | Optimized output |
| --- | --- | --- | --- | --- |
| Source-like identity, second level, `symbolic-independent-2d.loop` | exit 0 | `permutable-band` | absent | present |
| Mixed-depth second level, `matmul-init.loop` | exit 0 | `permutable-band` | absent | present |
| Diamond plus second level, `diamond-example-inner-batch.loop` | exit 0 | `permutable-band` | absent | present |
| Trailing-zero-normalized second-level OpenScop pair, `fusion7-second-level-zero-normalized.*.openscop` | exit 0 | `permutable-band` | absent | validated target accepted |

The complete second-level regression suite covers 53 specialized acceptances,
one standalone trailing-zero normalization boundary, a 20-case
diamond/current/strict matrix, and focused rejection checks. Every successful
case requires the direct route. The diamond matrix now separates 16 accepted
parallel/hinted compositions from four explicit vector-current hard failures;
the latter report no tiling route. The mixed-depth case retains an explicit
256/32 nested-output check.
The final isolated run after adding statementwise mixed-depth and interleaved
diamond recognition took `1029.41s` (`17:09`). The focused 20-case diamond
route matrix took `390.30s` (`6:30`). Earlier complete runs took `1040s` and
`954.751s`; retain the `1800s` outer timeout to account for container and host
load. The complete recheck after adding trailing-zero normalization took
`1063.03s` (`17:43`) while the other route matrices ran concurrently during
its first six minutes.

The separate Pluto compatibility matrix passed all 133 checks in `333.01s`
(`5:33`) in `gifted_curie`. A dedicated 90-case one-level route-discipline
matrix passed in `209s` (`3:29`). It ran ordinary, identity-tiled, diamond, and
full-diamond producers; ISS and non-ISS
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
2. broaden effect fixtures for heterogeneous and interleaved second-level
   schedules;
3. retain the proved fallback validators for valid schedules outside the
   direct checker's intended recognition language.

Fallback is retained, but direct permutable-band validation is now the required
route for every successful case in the advertised Pluto tiling matrix.
