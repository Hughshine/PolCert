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
`RawParallelCurrentMany*` config in the verified wrapper.

## Proof and artifact evidence

The last full code-artifact smoke was run on the pushed `end-to-end` state at
commit `72deba1`, tagged
`state-eq-polyhedral-verification-complete-2026-05-25`. Later `end-to-end`
commits may be documentation-only. That code state passed:

```sh
make -j4 artifact-check
```

That smoke includes the proof report, capability matrix, generated-C stride and
unroll/jam checks, the second-level suite, the diamond suite, and the Pluto
compatibility suite with 114 checks.

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
