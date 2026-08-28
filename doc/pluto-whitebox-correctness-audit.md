# Pluto White-Box Correctness Audit

Date: 2026-08-28

## Scope and Standard

This audit covers the Pluto optimizer pinned by PolCert:

- repository: `https://github.com/verif-scop/pluto.git`
- current fixed baseline: `56b66690edeed1ef17ddc018bbf67666795a3fd4`
- audited predecessor: `488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02`
- local audit tree: `/tmp/pluto-pinned-audit`

The question is compiler soundness, not whether a heuristic is profitable. A
finding is classified as:

- **reproduced miscompilation** when original and generated executables produce
  different observable results;
- **fail-open source path** when the code can construct or annotate an illegal
  schedule, but no executable witness has yet been minimized;
- **crash/undefined behavior** when malformed state or an option combination can
  corrupt memory or terminate the optimizer;
- **conservative/quality defect** when the implementation can reject or miss an
  optimization but does not enlarge the accepted transformation set.

Pluto is suitable for PolCert only as an untrusted candidate generator. This
audit does not support treating Pluto's generated C, dependence-satisfaction
bits, parallel metadata, or post-codegen rewrites as certificates.

## Reproduced Silent Miscompilations

### A Forced Affine Group Order Places a Consumer Before Its Producer

`lib/pluto.c:891-940` reads `.fst` and installs scalar statement groups
directly. Dependence satisfaction is then updated incrementally without an
independent final check that the complete lexicographic schedule preserves
every dependence. The minimized case in
`tests/pluto-bugs/affine-fst-reversed/` forces the consumer group before its
producer. Pluto exits successfully; the original prints `100`, while the
generated program prints `0`.

With Pluto's honest domain/access summaries, PolCert's standalone affine
schedule check rejects the before/after pair. More importantly, the complete
compatibility route imports only the candidate scattering, retains the source
instruction/domain/access data, raises an alarm, and emits no optimized loop.

### A Vanished Parallel Coordinate Is Transferred to a Dependent Loop

`tool/ast_transform.c:75-95` searches inner loops when a selected parallel loop
does not survive CLooG. Its boundary test uses `>` although a band with start
`depth` and width `width` ends before `depth + width`; the test must reject
`>=`. For a one-trip outer loop, CLooG removes the constant coordinate and the
fallback crosses a width-one parallel band into a recurrence-carrying loop.

The minimized case is in
`tests/pluto-bugs/vanished-outer-parallel/`. Pluto exits successfully and emits
an OpenMP `parallel for` on the recurrence. The original prints `10000`; three
four-thread executions of the generated program print `2499`. PolCert's strict
hint route rejects the vanished coordinate, and its explicit check of the
actual inner coordinate rejects the dependence.

### No-Tile Unroll-Jam Crosses a Non-Permutable Loop

`lib/polyloop.c:575-605` calls
`pluto_get_innermost_permutable_bands(prog, 1, ...)` unconditionally. The hard
coded tiled-level count is wrong under `--notile`; candidate enumeration then
selects a dependence-carrying loop below the true permutable band.
`tool/ast_transform.c:131-180` and the CLooG backend apply the selected jam
without another legality check.

The minimized case is in
`tests/pluto-bugs/notile-unrolljam-nonpermutable/`. The original completes one
inner `k` loop before advancing `j`. Pluto instead places `j` and `j+1`
statements adjacent inside `k`, causing a read before the producing `k=3`
iteration. The original prints `15`; Pluto's output prints `1`. PolCert applies
proved block unrolling but its local jam validation preserves separate `k`
loops, so it does not reproduce the unsafe rewrite.

### Inner-Parallel Tiling Metadata Marks a Dependent Loop Parallel

`lib/tile.c:446-478` moves dependence-satisfaction bits from inner dimensions
to the tile-space dimension under `--innerpar`, even though that mode does not
construct the corresponding wavefront schedule. The minimized two-dimensional
recurrence in `tests/pluto-bugs/tiling-innerpar-satvec/` uses tile size `2`.
The original deterministically prints `310235039`; repeated four-thread
executions of Pluto's output produce differing smaller values.

This case exposes a useful phase boundary. PolCert accepts the rectangular
tiling through the permutable-band theorem, then finds no certifiable parallel
dimension. Its non-strict route emits the correct sequential tiled loop; its
strict route rejects the requested parallel overlay and emits no optimized
loop. The defect is therefore in Pluto's tiling-to-parallel metadata handoff,
not a demonstrated failure of ordinary sequential strip-mining.

### Diamond Tiling Without Intra-Tile Optimization Skips a Required Restore

The phase-dump patch at predecessor commit `488ea2f` changed the diamond-only
call to `pluto_diamond_tile_reschedule` from unconditional to conditional on
`options->intratileopt`. That call restores a hyperplane temporarily evicted
while constructing the concurrent-start schedule. It is required before
Pluto's final CLooG/AST path and is distinct from the later optional intra-tile
locality pass.

The minimized FDTD-style case in
`tests/pluto-bugs/diamond-nointratile-reschedule/` disables parallelization,
vectorization, unroll-jam, and intra-tile optimization. The original prints
`20`; the affected diamond path printed `18`, and full-diamond printed `15`.
Ordinary and two-level rectangular tiling both print `20`, and sanitizers find
no undefined behavior in the witness. Pluto commit `56b6669` restores the
mandatory call and adds an upstream executable regression.

The same mixed-scalar `.loop` candidate is rejected by PolCert's formal tiling
boundary, and no optimized loop is emitted. The structural witness recovery
recognizes the floor links, but the extracted checker rejects the degenerate
scalar tile link. This is conservative rather than a diagnosis of the missing
backend restore. Separately, the typed `diamond-stencil` positive test accepts
a supported pure diamond mapping, validates its post-tiling affine schedule,
and generates Loop code through the proved path.

An independent pure-tiling matrix disabled parallelization, vectorization,
unroll-jam, and intra-tile optimization for every run. Ten integer kernels over
16 ordinary, two-level, partial-diamond, and full-diamond configurations gave
`160/160` matching checksums; symbolic and negative-offset cases added `80/80`
nonempty-domain and `21/21` empty-domain matches. This coverage found no second
pure-tiling wrong-code case, but it did expose two option-contract defects:
`--ft/--lt` does not restrict the tiled band, and two-level custom tile ratios
are misread when scalar schedule rows are interleaved with loop rows.

Run all executable witnesses and the checked PolCert outcomes with:

```sh
opam exec -- make test-pluto-bugs
```

## Per-File Assessment

| File | Reliability assessment | Defensive conclusion |
|---|---|---|
| `lib/pluto.c` | **High risk.** `.fst` and `.precut` are read implicitly at `891-1020` and directly install statement ordering or scattering with weak parsing and no final independent lexicographic legality check. `ddg_compute_cc` at `1983-2015` overwrites component identifiers for previously visited vertices; LP/DFP scaling can then scale the two ends of a real dependence independently. `pluto_auto_transform` restores identity on scheduling failure, but the CLI ignores its nonzero return. | Never trust its `dep->satisfied` state or final schedule. PolCert supports `.fst/.precut` only because it checks the resulting schedule and tiling witness independently. |
| `lib/framework.cpp` | **High risk.** `skipdeps.txt` at `361-418` silently removes legality constraints and has unchecked indices. A growing per-CC constraint width at `398-409` changes `ncols` without resizing storage. `get_feautrier_schedule_constraints` reads freed memory at `638-652`. `--typedfuse --nodepbound` can dereference a null `bounding_cst` at `1562-1586`. The per-CC objective index at `740-758` uses the wrong stride. ISL errors can be interpreted as empty constraints through `lib/constraints.c`. | Reject implicit `skipdeps.txt`; validate every returned affine schedule. Crashes are oracle failures, never permission to retain a partial candidate. |
| `lib/tile.c` | **Mixed, with two reproduced failures and one fixed in the current baseline.** Ordinary and two-level tiling consistently extend domains, schedules, accesses, original dependences, and transformed dependences, then recompute directions/satisfaction. `--innerpar` at `446-478` moves satisfaction bits even when it does not create the wavefront schedule, producing the reproduced wrong OpenMP program. The phase-dump patch also made a correctness-required diamond restore conditional on `intratileopt`; current commit `56b6669` fixes that defect. Diamond rescheduling at `93-107` still computes an evicted row offset from added domain dimensions and may miss inserted scalar schedule rows. `--ft/--lt` changes tile-size input count but does not restrict the actual tiled band. At `52-74`, the first-level tile-size parser skips scalar rows, while the second-level ratio parser consumes an integer for every band position and ignores `fscanf` failure; scalar-interleaved schedules therefore receive different second-level sizes from those requested. | Keep ordinary/two-level candidates behind the tiling theorem. Preserve the mandatory diamond restore, and independently validate parallel metadata, diamond mappings, and partial-level claims. Parse tile sizes against loop rows with checked input counts. |
| `lib/iss.c` | **High risk for multi-cut cases.** The dimension loop and cut-product loop reuse `i` at `654-684`, skipping dimensions after a second cut. More than two base cuts continue growing the bridge description while the actual partition stops at four regions. Late library use can also leave `transdeps` stale. | Accept ISS only when the emitted split and bridge witness agree and the extracted ISS checker proves the mapping. Do not infer correctness from Pluto's `base_cuts` alone. |
| `lib/post_transform.c` | **Conditionally reliable.** The standard schedule-only passes recompute dependence directions and satisfaction. Intratile interchange can cross scalar hyperplanes, but its callee swaps transformation rows without synchronizing hyperplane type metadata; several early returns also leak temporary loop arrays. | Revalidate the final post-tile affine schedule and reconstruct codegen metadata from the checked result. Memory leaks affect robustness, not semantics. |
| `lib/transforms.c` | **Unsafe as a general library surface.** `pluto_interchange` at `125-143` swaps schedule rows but not `hyp_types` or `hProps`, breaking metadata when crossing scalar rows. Exported `pluto_stripmine` writes column `ncols` and omits the usual `factor-1` upper-bound term; it currently has no caller in the pinned tree. | Do not expose these routines directly as trusted transformations. Validate the resulting schedule or keep the unused strip-mine API unreachable. |
| `lib/polyloop.c` | **High risk.** Parallel-loop discovery trusts mutable satisfaction vectors. The hard-coded tiled-level argument in unroll-jam selection causes the reproduced no-tile miscompilation. Parallel-band construction is also the producer consumed by the vanished-loop AST fallback. | Treat bands and loop annotations as hints only. Recheck the concrete surviving loop and every local jam candidate. |
| `lib/plutolib.c` | **Incomplete and unsafe API contract.** Unlike the CLI it propagates `pluto_auto_transform` failure, but it omits the main ISS phase even when requested. `pluto_parallel_schedule_with_remapping` does not initialize its advertised loop outputs, while `pluto_schedule_str` consumes them. Several public paths dereference null transforms or remappings after failure. | The library API is not a semantic substitute for the audited CLI pipeline. Fail immediately on null/failed transformations, initialize every output, and document unsupported phases. |
| `lib/program.cpp` | **Mostly conservative import, but unsafe as a mutable public IR.** Dependence div removal overapproximates and is conservative. Piecewise access extraction keeps one affine access for heuristics while exact ISL dependences remain authoritative. Dimension/parameter removal does not update all cached `bounding_poly` and `transdeps` objects, so nonstandard mutator orders can leave inconsistent shapes. The ambient `codegen.context` file can silently restrict CLooG's generated parameter domain. | Reject implicit `codegen.context`. Keep public mutators out of the verified path unless every dependent cache is rebuilt. Generate code from PolCert's checked IR rather than Pluto's context-restricted C. |
| `lib/ddg.c` | **Quality defect, not a known fail-open.** `compute_transitive_closure` at `103-112` uses `i,j,k`, not Floyd-Warshall's `k,i,j`, and misses paths. Its current use adds conservative distribution conflicts, so the observed effect is lost optimization. The Kosaraju SCC implementation itself is structurally sound. | Fix the closure, but do not rank it with the illegal-schedule findings unless a relaxing caller is introduced. |
| `tool/main.cpp` | **Weak failure discipline with a confirmed bad parameter path.** `--ufactor` uses unchecked `atoi` at `413-415`; zero or nonnumeric input becomes factor zero and Pluto emits loops extending past the original upper bound. It also ignores the return from `pluto_auto_transform` and continues after identity fallback, ignores codegen failure, and describes defaults differently from the implementation. | Validate numeric ranges and propagate every phase failure. PolOpt already rejects non-positive and nonnumeric `--ufactor`; regression tests make that boundary explicit. |
| `tool/osl_pluto.c` | **High risk.** The pinned tree contains the Candl dependence-type fall-through fix, but statement union domains are imported from only the first relation at `721-781`. MAY_WRITE is merged with definite WRITE before last-writer dependence construction, which can incorrectly kill an earlier writer. Ambient `.linearized/.nonlinearized` files at `1709-1729` replace statement text by substring without rebuilding accesses/dependences. ISS population also assumes a one-to-one Pluto/OSL statement list. | Reject ambient rewrite files, non-convex union-domain inputs that cannot be preserved, and unsupported may-write/state-changing semantics. Importer failures must be fatal. Scalar privatization remains outside PolCert's accepted surface. |
| `tool/ast_transform.c` | **Confirmed unsafe.** It contains the vanished-loop parallel miscompilation and applies unroll-jam candidates without a legality check. OpenMP private-variable construction uses a fixed 512-byte buffer. Vector and parallel markers are mutable backend metadata rather than semantic evidence. | Never accept AST annotations as certificates. Match them to surviving checked dimensions, and reject a hint that cannot be mapped exactly. |
| `tool/pluto_codegen_if.c` | **Backend consumer, not a validator.** It trusts schedule/hyperplane annotations established earlier and invokes CLooG plus AST rewrites. All generated iterators and bounds are hard-coded as C `int` without proving affine bounds fit; large parameter domains can overflow or truncate. CLooG return values are unchecked, and fixed-size metadata buffers can overflow for deep schedules. The similarly named `lib/pluto_codegen_if.c` is not the built tool implementation. | PolCert must not compile or validate by trusting this generated C; it uses its own proved code generator after validation. Pluto needs an integer-range contract or a wider checked codegen type. |
| `lib/constraints.c` | **High-risk error handling.** `pluto_constraints_is_empty` at `1903-1917` stores ISL's tri-state result in C `bool`; `isl_bool_error == -1` becomes true and can make solver failure look like an empty violation set. | Preserve the ISL error state and fail closed. A solver error must not establish dependence satisfaction or direction. |

## Important Source Paths Without Executable Witnesses

The following paths are strong enough to fix or gate, but are not labeled
reproduced miscompilations:

1. diamond rescheduling can restore an evicted hyperplane to the wrong row when
   a selected band contains scalar hyperplanes.
2. `skipdeps.txt` and `.precut` can bypass the invariant that every
   earlier schedule component is nonnegative before a later component satisfies
   a dependence.
3. incorrect DDG connected components can invalidate independent LP/DFP
   rational-schedule scaling.
4. ISL errors can be misclassified as proofs of emptiness.

Separate confirmed robustness defects include the per-CC storage overrun, the
Feautrier UAF, the `--typedfuse --nodepbound` null dereference, unchecked legacy
control-file parsers, and fixed-size codegen buffers. These can stop or corrupt
the untrusted oracle; they do not become accepted PolCert transformations
without a successful parser and validator result.

## What PolCert Catches

PolCert does not attempt to prove Pluto. It narrows Pluto's role at each
boundary:

1. affine schedules are accepted only after dependence legality validation;
2. ISS is accepted only through the checked source-to-split witness;
3. ordinary, two-level, and diamond tiling use checked tiling witnesses rather
   than Pluto's satisfaction bits;
4. post-tile affine rescheduling is validated as a separate schedule change;
5. parallel and vector annotations require a fresh check of the concrete loop
   dimension;
6. unroll-jam uses proved unrolling plus local trace-permutability validation;
7. final Loop code is generated by PolCert, not copied from Pluto's CLooG/AST
   backend.

This separation rejects or removes the unsafe transformation in the four
unfixed witnesses. For the fixed pure-diamond witness, the corresponding
mixed-scalar PolCert route rejects and emits no optimized loop; supported typed
diamond candidates use PolCert's proved generator rather than Pluto's backend.
It also blocks illegal affine schedules arising
from hidden dependence controls, LP scaling, or stale satisfaction metadata,
provided the candidate stays within PolCert's modeled IR. It does not certify
arbitrary Pluto-generated C, SIMD instructions, scalar privatization, storage
expansion, or transformations that change the number or meaning of program
states.

## Defensive Actions in This Artifact

- CI executes the four remaining producer miscompilation witnesses, the fixed
  pure-diamond regression, and the corresponding PolCert outcomes. The legacy
  shard also runs the accepted typed pure-diamond positive case.
- `driver/Scheduler.ml` rejects ambient `skipdeps.txt`, `codegen.context`,
  `.linearized`, and `.nonlinearized`.
- Legacy `tile.sizes`, `.fst`, and `.precut` remain compatible only because
  their resulting transformations pass the corresponding checked boundary;
  explicit file options remain preferable for reproducibility.
- The Pluto commit and image digest remain pinned and checked before tests.

The ISS suite additionally fixes a valid two-cut/four-piece bridge and two
negative variants. The extracted complete-cut-shape checker accepts the full
sign partition, rejects a Pluto-style three-cut/four-piece mismatch, and
rejects a two-cut witness with one sign region missing. This exercises the
semantic boundary that PolCert uses instead of trusting Pluto's `base_cuts`
bookkeeping.

The standalone `--validate-affine-openscop` action has a deliberately narrower
contract than complete compilation. It checks schedule refinement under the
domains and access summaries supplied by the OpenScop inputs; its importer
omits statement bodies and cannot establish that those summaries describe
arbitrary C text. The complete `.loop` route does not inherit this assumption:
it imports only Pluto's scattering and retains the source instruction, domain,
and access data.

The remaining Pluto-side priority is to fix the four reproduced defects, then
add an independent final lexicographic legality gate inside Pluto itself. On the
PolCert side, scalar-band diamond, LP/DFP, and implicit legacy-control
combinations should gain the same explicit adversarial coverage now used for
`--innerpar` and multi-cut ISS.
