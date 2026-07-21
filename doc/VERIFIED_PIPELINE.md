# Verified Pipeline

This note records the current theorem-facing `polopt` pipeline. It is a compact
orientation document; detailed flag coverage lives in
`doc/pluto-polopt-compatibility.md` and `doc/POLOPT_FLAG_GUIDE.md`.

## Current contract

The main compiler wrapper is the extracted Coq compiler:

```text
VerifiedParallelCompilerConfig.compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

The paper-level theorem is `VerifiedParallelCompilerConfig.compile_correct`.
For any accepted `raw_config`, if the compiler returns a `ParallelLoop.t` target,
every terminating target execution is matched by a source `Loop.t` execution with
`State.eq` final states. `compile_verified_correct` is the corresponding theorem
after `check_config` has accepted a verified config.

Sequential routes are not outside this theorem. They are lifted into
`ParallelLoop.t` with all-`SeqMode` annotations. Parallel routes return the same
target language with checked `ParMode` annotations.

## Executable `polopt` shape

A normal schedule, tiling, or parallel optimizer run has this shape:

```text
.loop text
-> parser / elaborator
-> Loop.t
-> Pluto-compatible flag filtering and route normalization
-> optional Pluto oracle calls for schedules, tiling phases, or annotations
-> checked route construction
-> VerifiedParallelCompilerConfig.compile
-> ParallelLoop.t
-> printer / generated-loop checks
```

Pluto is an oracle: it proposes schedules, phase outputs, and loop annotation
hints. PolOpt accepts those artifacts only through checked routes.

For a tiling boundary, the extracted dispatcher first tries a direct semantic
permutable-band check. It checks source-ordered WW, WR, and RW conflicts with
the same prefix before the band for decreases in the selected band components,
using certified polyhedral emptiness queries. A successful direct check reports
`permutable-band`. If the direct checker returns `false` because the layout is
outside its recognizer or the property is not established,
the dispatcher tries proved legacy, canonical, and general tiling validators;
successful acceptance reports `general-fallback`. No accepted fallback is
relabeled as a band result. An impure solver alarm propagates instead of
triggering fallback.

This check is a semantic analogue of Pluto's fully permutable-band condition
for recognized layouts. It is not a verification of Pluto's band detector,
independent-hyperplane search, or optimization heuristics. The implementation
reuses the affine validator's certified conflict and emptiness kernels, but it
does not call the whole affine-schedule validator. Ordinary rectangular,
diamond, full-diamond, and recognized grouped/interleaved second-level layouts
can use the direct route. Source-like identity layouts and structurally
unmatched mixed-depth layouts may use the proved fallback. Diamond pipelines
validate their final affine leg
separately, and that leg is checked by `validate_general`.

The important route families are:

- sequential configs through `RawSeq`, including identity, affine-only, ordinary
  tiling, ISS, second-level tiling, diamond, and full-diamond compositions
  supported by the current wrapper;
- explicit one-current parallel configs such as `RawParallelCurrentDefault d`;
- Pluto-hinted one-current parallel configs selected by `--parallel`;
- Pluto-hinted multi-current parallel configs selected by `--parallel --multipar`
  and represented by the `RawParallelCurrentMany*` constructors.

Vector and unroll/jam are checked adjacent routes, not constructors of
`VerifiedParallelCompilerConfig.raw_config`. Vector routes reuse the doall
certificate and the checked vector codegen lemmas. The supported unroll/jam
route is a checked Loop-level postpass applied by the OCaml driver around the
sequential Loop optimizer result before lifting/printing.

## Pluto-compatible CLI

`./polopt --pluto-compat ... file.loop` accepts Pluto-style flags, rejects
unsupported combinations with explicit reasons, and dispatches the accepted
combination to the relevant checked route. The unified wrapper covers ordinary
tiling, second-level tiling, ISS combinations, diamond and full-diamond routes,
checked parallelization, and `--multipar` up to the current multi-current
certificate surface. Adjacent checked routes cover vector annotation and the
supported unroll/jam subset.

`--multipar` is no longer a side printer path. The driver parses Pluto's
parallel-loop hints, builds a list of candidate current dimensions, and calls a
`RawParallelCurrentMany*` config in the verified wrapper. It submits every
dimension in the finite candidate list constructed for that route; no
two-element truncation remains. Vector routes are
innermost-only: hinted mode does not search other dimensions, and explicit
`--vector-current` rejects a non-innermost selection.

## Proof and artifact evidence

The direct-band integration is not represented by the older May 2026 artifact
record. The release procedure must run the full claim suite on the final v3 tag
and record its commit, image digest, route summary, and raw result bundle. A
pre-freeze integration run passed the 138-case Pluto compatibility suite; it is
not a substitute for the final image review.

## Boundary

The current theorem family is state-preserving. The unified wrapper covers
schedule, tiling, ISS, diamond, second-level, and checked parallel annotation
routes that preserve the same observable storage under `State.eq`; adjacent
checked vector and unroll/jam routes use their own theorem-backed components. It
deliberately does not cover storage-changing transformations such as scalar
privatization, array contraction, layout remapping, or overlapped / reuse-based
tiling. Those need a separate state relation rather than another flag in the
current wrapper.

Untrusted or non-theorem parts remain outside the Coq theorem: Pluto's search
heuristics, textual parsing and printing, OpenScop engineering, and witness
inference from external files. Those components are either treated as proposal
generators or as frontend/backend engineering around the checked core.
