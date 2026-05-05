# Pluto-Polopt Compatibility Surface

Date: 2026-05-05

Audience: PolCert developers who need to align `polopt` with Pluto as the reference optimizer.

## Purpose

`polopt` should be understood as a Pluto-compatible checked subset, not as a separate optimizer with unrelated flags. The intended architecture is:

```text
Pluto-like optimizer flags
  -> polopt flag normalizer
  -> capability filter with explicit rejection reasons
  -> Pluto used only as optimization oracle
  -> validator/import/codegen in polopt
```

This document records what is supported, what is not supported, why it is not supported, and how each unsupported part could be supported.

The main design point is that Pluto's CLI mixes several layers:

- frontend extraction
- dependence analysis and solver selection
- affine scheduling and fusion
- tiling and tile scheduling
- code generation and post-codegen rewrites

`polopt` should align with Pluto's optimizer-facing surface. It should reject Pluto flags that belong to Pluto's frontend or codegen surface, unless `polopt` implements an equivalent checked feature.

## Evidence Used

The current assessment is based on these concrete checks.

- Pluto source inspection in `/pluto`:
  - `tool/main.cpp`: option parser, normalization rules, main pass order
  - `lib/program.cpp`: actual default values
  - `lib/pluto.c`: affine scheduling, fusion, custom `.fst/.precut`, diamond insertion
  - `lib/tile.c`: tiling, second-level tiling, tile scheduling, intra-tile optimization
  - `lib/iss.c`: ISS restrictions
  - `tool/pluto_codegen_if.c` and `tool/ast_transform.c`: OpenMP, vector, unroll-jam marking
- Current Pluto baseline build:
  - `/pluto` HEAD: `6f43860b6c4cddeeca09189bf3073f05b78b14a5`
  - `pluto --version`: `PLUTO version 6f43860`
  - configured with `./configure --enable-glpk --with-glpk-prefix=/usr`
  - `pluto --help` advertises `--glpk`, `--lp`, `--dfp`, and `--typedfuse`
  - PolCert's Dockerfile checks out this commit and rebuilds `/pluto` with GLPK before building PolCert
- Candl probe:
  - original `/pluto/tool/pluto --candldep` aborted on `matmul.c`, `fusion1.c`, and Candl's `scalpriv.c`
  - root cause: `tool/osl_pluto.c:deps_read` converted Candl dependence types with fall-through, so recognized Candl dependences became `PLUTO_DEP_UNDEFINED`
  - fix applied in the Pluto checkout: add `break` statements and import `OSL_DEPENDENCE_RAW_SCALPRIV` as a Pluto RAW dependence
  - after rebuilding `/pluto`, `--candldep` and `--candldep --scalpriv` return successfully on `matmul.c`, `fusion1.c`, `nodep.c`, and Candl's `scalpriv.c`
- Current `polopt` route inspection:
  - `syntax/SLoopRoute.ml`: route normalization and explicit rejections
  - `driver/Scheduler.ml`: actual Pluto flag recipes sent by `polopt`
- Executed native compatibility mode:
  - public entry: `./polopt --pluto-compat`
  - implementation: `syntax/SLoopCli.ml` and `syntax/SLoopRoute.ml`
  - `tools/polopt_flag_suites/run_pluto_compat_suite.py`
  - default GLPK-enabled Pluto baseline result: `74 / 74` checks passed
- Executed diamond validation suite:
  - `make test-diamond-tiling-suite`
  - result: 6 diamond-effect cases validated, 2 no-effect cases validated, 11 unsupported Pluto inputs rejected as expected
- Executed artifact smoke check:
  - `make artifact-check`
  - result: py-compile, proof report, capability matrix, Pluto-compatible suite, second-level suite, and diamond suite all passed

One important correction: Pluto's `--help` is not reliable for defaults in this build. The help text says some features are disabled by default, but `lib/program.cpp` initializes `tile=1`, `parallel=1`, `diamondtile=1`, `intratileopt=1`, `prevector=1`, `unrolljam=1`, and `smartfuse`.

## Status Classes

This document uses five status classes.

| Status | Meaning |
|---|---|
| Supported | Current `polopt` exposes a checked route and tests exercise it. |
| Surface gap | Pluto can express it and current validators likely suffice, but `polopt` does not yet expose the flag or route. |
| Composition gap | Existing validators cover pieces, but the requested flag combination needs a new composed route, witness plumbing, or theorem invocation sequence. |
| Validator/semantic gap | Supporting it needs a new validator, codegen proof, or operational semantics argument. |
| Out of optimizer surface | The flag belongs to Pluto's frontend, backend, or stale scripts. `polopt` should not expose it as an optimizer flag. |

## Supported Optimizer Surface

The supported surface is already nontrivial.

| Pluto-style request | Current `polopt` behavior | Evidence |
|---|---|---|
| Default full tiled route | Runs checked affine + ordinary band-aware tiling route. | generated suite and native compat `ordinary-tiled` |
| `--notile` | Runs affine-only checked route. | native compat `affine-only` |
| `--identity --notile` | Runs no-Pluto identity extraction/codegen route. | existing CLI route |
| `--identity --tile` | Runs the checked identity-tiling route: identity extraction followed by Pluto's tile-only phase and the existing tiling validator/codegen chain. This gives a real tiling effect when the original schedule already exposes a directly tileable band. | native compat `identity-tiled`; `SBandTilingOpt.opt_identity_tiled`; `Opt_identity_tiled_band_correct` |
| `--identity --tile --parallel`, `--identity --tile --parallel --multipar` | Runs the same checked identity tiling boundary, then feeds Pluto's parallel loop hint(s) to the extracted checked parallel validator/codegen path. The explicit-current native route has a Coq theorem-facing entry as well. The positive fixture shows 32x32 identity tiling plus one or two `parallel for` annotations. | native compat `identity-tiled-parallel`, `identity-tiled-multipar`; `Opt_parallel_current_identity_tiled_result_correct`; extracted tiling and parallel validators/codegen |
| `--identity --tile --iss` | Runs checked ISS complete-cut recovery, then checked identity tiling over the split program. Current tests show the tiling effect remains available under `--iss`; the current `.loop` corpus did not contain a case where ISS uniquely enables identity tiling. | native compat `identity-tiled-iss`; `SBandTilingOpt.opt_identity_tiled_with_iss`; `Opt_identity_tiled_band_with_iss_correct` |
| `--iss` | Runs ISS + affine + tiling route when the input satisfies ISS shape constraints. | existing ISS suite |
| `--second-level-tile` | Runs checked second-level tiling route on full tiled paths. | native compat `second-level`; second-level suite |
| `--iss --second-level-tile` | Runs the sequential ISS + second-level route; the focused native compat case shows the expected two-level tile shape. | native compat `second-level-iss` |
| `--parallel` | Runs Pluto-hinted checked parallel route for one parallel loop. | native compat `parallel`; parallel tests |
| `--parallel-current d` | Runs explicit-dimension checked parallel route. The native `--identity-tiled --parallel-current d` form exercises the extracted identity-tiling plus explicit-current theorem route without pretending that `--parallel-current` is a Pluto flag. | parallel-current suite; `identity-tiled-current-combined-effect` |
| `--prevector`, `--vector` | Runs a checked vector annotation route. Pluto's vector marking is derived from the same parallel-loop analysis used for `--parallel`, so PolOpt reuses the parallel/doall checker and emits `vector for`. | native compat `prevector`; `checked_vector_annotated_codegen_correct_general`; vector-current suite |
| `--vector-current d` | Runs explicit-dimension checked vector annotation. This is a native PolOpt theorem-facing route, not a Pluto flag. | vector-current suite |
| `--diamond-tile` | Runs sequential diamond phase-aligned route on default full tiled path. | native compat `diamond`; diamond suite |
| `--full-diamond-tile` | Runs stronger diamond producer mode on the same checked route. | native compat `full-diamond` |
| `--smartfuse` | Passed through to Pluto's checked scheduler oracle; this is also the default fusion policy in current recipes. | native compat `ordinary-tiled`; oracle flag note |
| `--nofuse` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-nofuse-affine`; differs from smartfuse baseline |
| `--maxfuse` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-maxfuse-affine`; differs from smartfuse baseline |
| `--nodepbound` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-nodepbound-affine`; differs from smartfuse baseline |
| `--per-cc-obj` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-per-cc-obj-affine`; differs from smartfuse baseline |
| `--flic`, `--fast-lin-ind-check` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-flic-affine` and `optimizer-fast-lin-ind-check-affine`; differ from smartfuse baseline |
| `--determine-tile-size` | Passed through to Pluto's checked scheduler oracle on tiled routes. | native compat `optimizer-determine-tile-size`; differs from fixed-size tiling baseline |
| `--cache-size <n>`, `--data-element-size <n>` | Passed through to Pluto's checked scheduler oracle when paired with `--determine-tile-size` on tiled routes. | native compat `optimizer-cache-size` and `optimizer-data-element-size`; differ from automatic tile-size baseline |
| `--intratileopt` | Passed through to Pluto's checked scheduler oracle as the explicit alternative to `--nointratileopt`. | native compat `optimizer-intratileopt`; standalone affine+tiling validators pass on intratileopt fixtures |
| `--lastwriter` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-lastwriter-affine`; differs from default dependence mode baseline |
| `--nolastwriter` | Passed through to Pluto's checked scheduler oracle and rejected if combined with `--lastwriter`. | native compat `optimizer-nolastwriter-affine` |
| `--candldep` | Conditionally passed through when the selected Pluto binary passes a dependent Candl smoke probe. The current `/pluto` baseline has the Candl importer fix. | direct Pluto Candl smoke checks; native compat `optimizer-candldep-affine`; rejects `--candldep --lastwriter` and `--isldep --candldep` |
| `--candldep --scalpriv` | Conservatively passed through to Pluto's checked scheduler oracle. PolOpt does not generate private scalar storage; it accepts only schedules that still validate under the original scalar storage semantics. | native compat `optimizer-candldep-scalpriv-affine`; rejects bare `--scalpriv` |
| `--isldepaccesswise`, `--isldepstmtwise`, `--isldepcoalesce` | Passed through to Pluto's checked scheduler oracle. | native compat dependence-tuning checks; direct Pluto smoke checks on `matmul.c`, `fusion1.c`, and `nodep.c` |
| `--pipsolve` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-pipsolve-affine`; direct Pluto smoke checks on `matmul.c`, `fusion1.c`, and `nodep.c` |
| `--coeff-bound <n>` | Passed through to Pluto's checked scheduler oracle as a positive integer value. | native compat `optimizer-coeff-bound-affine`; direct Pluto smoke checks |
| `--ft <n>`, `--lt <n>` | Passed through together on tiled routes as non-negative partial tiling-level controls. | native compat `partial-tiling-levels`; direct Pluto smoke checks |
| `--forceparallel <bitvec>` | Passed through as a non-negative value. The pinned Pluto source accepts it but has no effective use site. | native compat `optimizer-forceparallel-pass-through`; Pluto source grep |
| `--glpk`, `--lp`, `--dfp`, `--ilp`, `--lpcolor`, `--clusterscc`, `--typedfuse`, `--hybridfuse`, `--delayedcut` | Passed through on the pinned GLPK-enabled Pluto baseline, with a runtime rejection if an alternate Pluto binary lacks LP/DFP support. | native compat GLPK-family affine checks; effect checks against the smartfuse baseline |
| `--rar` | Compatible with current scheduler recipes. | scheduler flags |
| `--nointratileopt`, `--noprevector`, `--nounrolljam`, `--noparallel`, `--nodiamond-tile` | Accepted when they match the checked route's disabled Pluto-side effects. `--noprevector` disables vector annotation; omitting it keeps Pluto's default `--prevector` and selects the checked vector route. | native compat suite |

The current default `polopt` route is not "Pluto default". It intentionally uses phase-aligned recipes. For ordinary sequential optimization, it runs an affine-only Pluto phase with tiling and codegen effects disabled, then a tile-only Pluto phase with `--identity --tile`. This makes the output easier to validate because affine scheduling and tiling are separated.

The bare Pluto flag `--identity` needs special care. In the current Pluto source, tiling is enabled by default, so `--identity` can still reach the tiling phase. The compatible `polopt` no-tiling identity route is therefore modeled as `--identity --notile`. Plain sequential `--identity --tile` has its own theorem-facing route: it exports the identity schedule, runs Pluto's tile-only phase, and validates the tiling boundary before code generation. This route is intentionally narrower than the default affine+tiling route: it tiles programs whose source-order band is already accepted by the band validator, while programs that need Pluto's affine scheduling first still belong to the default route. The `--identity --tile --parallel` route now composes that checked tiling boundary with the existing extracted checked parallel validator/codegen path; `--multipar` can certify up to two dimensions when the validated current-space program supports them. The `--identity --tile --iss` form has the corresponding theorem-facing composition with ISS split validation first; it is supported, but current tests do not claim an ISS-sensitive extra tiling effect.

The compatibility mode also requires callers to say how they want to handle Pluto defaults. A bare invocation is rejected. The caller must explicitly handle intratile optimization and unroll-jam with `--nointratileopt` or `--intratileopt`, and `--nounrolljam`; must choose either `--noparallel` or `--parallel`; and must choose either `--nodiamond-tile` or a diamond route. For vectorization, Pluto's default-on `--prevector` now maps to PolOpt's checked vector route, while `--noprevector` disables that annotation.

The public artifact-facing entry point is native in `polopt`:

```bash
./polopt --pluto-compat [--explain] <Pluto-like flags> file.loop
```

For example:

```bash
./polopt --pluto-compat --explain \
  --tile --smartfuse --nointratileopt --noprevector --nounrolljam \
  --rar --nodiamond-tile --noparallel \
  tests/polopt-generated/inputs/matmul.loop
```

This command still uses `polopt`'s verified extraction and code generation. The
native driver filters Pluto-style optimizer flags, maps the accepted subset to
checked `polopt` routes, and prints a specific reason for rejected flags or
combinations.

## Frontend and Input Flags

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--pet` | Unsupported | `polopt` uses its own loop extractor. PET would change the frontend and the source model being validated. | Not as an optimizer flag. | Keep rejecting. If PET input is desired, add a separate importer mode with its own source-model contract. |
| `--readscop` | Unsupported | `polopt` user input is `.loop`, not arbitrary OpenScop. | Possible as a separate validator/debug mode. | Add `polopt --input-openscop` or a standalone validation action. Do not mix it with normal `.loop` compilation. |
| `--dumpscop` | Unsupported as user flag | Pluto dumps are internal oracle artifacts. `polopt` already has explicit validation actions for OpenScop pairs. | Possible as debug output. | Add `--dump-oracle-scops` that names before/mid/posttile/after files. Keep it distinct from Pluto's exact `--dumpscop` semantics. |

These are not proof limitations. They are interface-boundary choices.

## Codegen and Post-Codegen Flags

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--prevector` | Supported narrow | Pluto records vector loops as OpenScop loop directives. PolOpt parses directive bit `4`, then reuses the checked parallel/doall certificate to emit `vector for`. If Pluto's hinted current dimension is not certifiable, non-strict mode scans for a certifiable current dimension and reports a checked warning. | Already supported by the checked vector annotation route. | Add specialized vector checkers only if future semantics need fixed-width SIMD, reductions, or backend-specific pragmas. |
| `--noprevector` | Compatible no-op | Disables checked vector annotation. | Already acceptable. | Keep as no-op with explanation. |
| `--unrolljam` | Unsupported | Pluto performs loop-body rewriting after codegen. This is not a schedule-only oracle effect. | Yes, but requires new validation/proof. | Implement checked unroll-and-jam as a `polopt` transformation or add a validator for Pluto's unrolled AST/code. |
| `--nounrolljam` | Compatible no-op | Current checked recipes already disable Pluto unroll-jam. | Already acceptable. | Keep as no-op with explanation. |
| `--ufactor` | Unsupported | Only meaningful with `--unrolljam`. | Depends on unroll-jam support. | Add after checked unroll-jam exists. |
| `--cloogsh`, `--cloogf`, `--cloogl` | Unsupported | These tune Cloog code generation, which `polopt` does not use as trusted output. | Not as optimizer flags. | Only expose equivalent `polopt` codegen knobs if needed. |
| `--nocloogbacktrack` | Compatible no-op in native compatibility mode | It only constrains Pluto/Cloog code generation, which `polopt` discards. Accepting it avoids rejecting a harmless disabling flag. | Already acceptable as no-op. | Keep the native note explicit so users do not infer Cloog output is validated. |
| `--codegen-context` | Unsupported | This shapes Pluto/Cloog generated bounds. `polopt` regenerates code itself. | Possible as a `polopt` codegen knob. | Add a checked codegen context option if the loop language needs it. |
| `--bee`, `--indent`, `-o` | Unsupported in native compatibility mode | These are backend/output concerns. | Possible under `polopt` names. | Add `polopt` output formatting/path options separately from optimizer compatibility. |

These are mostly not "missing Pluto optimization". They are backend features. A direct Pluto probe on `matmul.loop` shows that `--prevector` adds an OpenScop `<loop>` extension with directive `4`; PolOpt now imports that directive as a checked vector annotation. The same probe did not change the dumped schedule for `--unrolljam`, but the Pluto source applies unroll-jam to the CLAST/codegen path and records unroll metadata when hyperplanes are marked. Supporting unroll-jam as a positive result would therefore require a checked `polopt` codegen feature, not just oracle pass-through.

The vector path deliberately follows the checked parallel route: recover or choose a vectorizable loop, validate the doall precondition, and emit a checked vector annotation. This is sound for Pluto-style prevectorization because Pluto's vector marker is derived from parallel loop analysis. A realistic unroll-jam path is separate: it needs a checked post pass over `polopt`'s loop IR, with factor handling, remainder generation, and a semantic preservation theorem. The disabling flags `--noprevector` and `--nounrolljam` remain accepted because they are how callers turn off Pluto's default codegen-side behavior for checked routes.

## DFP and Typed Fusion

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--typedfuse` | Supported on the pinned baseline | The pinned Pluto baseline advertises GLPK/DFP support; the suite validates a representative affine case with a visible shifted loop nest. | Already supported when the selected Pluto binary advertises GLPK or Gurobi. | Keep the runtime probe. Broaden effect fixtures beyond `matmul.loop`. |
| `--hybridfuse` | Supported on the pinned baseline | Same binary capability requirement as typed fusion; the suite validates a representative affine case with the DFP-style loop nest. | Already supported when the selected Pluto binary advertises GLPK or Gurobi. | Broaden effect fixtures beyond `matmul.loop`. |
| `--delayedcut` | Supported on the pinned baseline | DFP-only option; the suite validates `--glpk --dfp --delayedcut` on a representative affine case. | Already supported when the selected Pluto binary advertises GLPK or Gurobi. | Broaden effect fixtures beyond `matmul.loop`. |
| `--dfp`, `--lp`, `--ilp`, `--lpcolor`, `--clusterscc` | Supported on the pinned baseline | The pinned Pluto baseline advertises these LP/DFP controls, and native compatibility tests validate representative affine cases. | Already supported when the selected Pluto binary advertises the option. | Keep runtime rejection for alternate Pluto binaries that lack LP/DFP support. |
| `--glpk` | Supported on the pinned baseline | The PolCert Dockerfile rebuilds Pluto with `--enable-glpk --with-glpk-prefix=/usr`; the checker requires `--glpk`, `--lp`, and `--dfp` in `pluto --help`. | Already supported when the selected Pluto binary advertises `--glpk`. | Treat as oracle solver selection; validator remains the correctness gate. |
| `--gurobi` | Conditional support | Not available in the current container. | Supported only if a selected Pluto binary advertises `--gurobi`. | Same as `--glpk`, but requires a Gurobi-enabled build. |

This category is now default artifact behavior for GLPK-backed Pluto. If DFP or typed fusion only changes which affine schedule Pluto finds, the existing affine validator is the central correctness check. The suite checks a visible schedule effect on `matmul.loop`: `--glpk`, `--glpk --ilp`, `--glpk --lp`, `--glpk --lpcolor`, and `--glpk --clusterscc` select the direct `M,N,K` loop order, while `--glpk --dfp`, `--typedfuse --glpk`, `--glpk --hybridfuse`, and `--glpk --dfp --delayedcut` produce the shifted DFP-style loop nest. The remaining work is finding non-matmul effect fixtures.

## Fusion and Scheduling Objective Knobs

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--nofuse` | Supported as oracle tuning | Native compatibility mode appends it to Pluto scheduler calls after the default recipe flags. | Already supported for checked routes whose produced schedule validates. | Keep effect tests; broaden beyond affine-only fusion fixtures. |
| `--maxfuse` | Supported as oracle tuning | Same pass-through mechanism as `--nofuse`. | Already supported for checked routes whose produced schedule validates. | Keep effect tests; broaden beyond affine-only fusion fixtures. |
| `--smartfuse` | Supported as oracle tuning/default | Current recipes use it by default, and explicit `--smartfuse` is preserved in the Pluto oracle flag stream. | Already supported. | Keep explicit acceptance and ordering behavior. |
| `--per-cc-obj` | Supported as oracle tuning | Native compatibility mode appends it to Pluto scheduler calls; `pca.loop` demonstrates a schedule/codegen difference from smartfuse baseline. | Already supported for checked routes whose produced schedule validates. | Broaden fixtures and check interactions with tiling/diamond routes. |
| `.fst`, `--fusion-structure FILE`, `--fst-file FILE` | Supported as Pluto legacy implicit file and explicit PolOpt compatibility input | Pluto reads `.fst` from the working directory and uses it to force a statement partition for fusion or distribution. PolOpt can now install that file explicitly for the Pluto oracle call and remove it afterward. The produced schedule is accepted only when the checked affine validator accepts it. | native compat `optimizer-implicit-fst-file`, `optimizer-explicit-fst-file` | Prefer the explicit file option in artifact scripts. |
| `.precut`, `--precut-file FILE`, `--precut FILE` | Supported as Pluto legacy implicit file and explicit PolOpt compatibility input | Pluto reads `.precut` from the working directory and uses it as a partial transformation for Pluto to complete. PolOpt can now install that file explicitly for the Pluto oracle call and remove it afterward. The produced schedule is accepted only when the checked affine and tiling validators accept it. | native compat `optimizer-implicit-precut-file`, `optimizer-explicit-precut-file` | Prefer the explicit file option in artifact scripts. |
| `--nodepbound` | Supported as oracle tuning | Native compatibility mode appends it to Pluto scheduler calls; `fusion2.loop` demonstrates a schedule/codegen difference from smartfuse baseline. | Already supported for checked routes whose produced schedule validates. | Broaden fixtures and check interactions with tiling/diamond routes. |
| `--coeff-bound` | Supported as oracle tuning | Search-bound tuning with a positive integer value. | Already supported for checked routes whose produced schedule validates. | Keep the tight-bound effect fixture and broaden value choices. |
| `--fast-lin-ind-check`, `--flic` | Supported as oracle tuning | Native compatibility mode appends either alias to Pluto scheduler calls; `costfunc.loop` demonstrates a schedule/codegen difference from smartfuse baseline. | Already supported for checked routes whose produced schedule validates. | Keep both aliases covered; broaden beyond the current cost-function case. |

`--coeff-bound` should not require new proof principles if the output remains an affine schedule accepted by the current affine validator. The suite now includes a tight-bound effect case on `fusion10.loop`: `--coeff-bound=1` forces a simpler schedule than the default smart-fusion affine schedule. Additional fixtures can still broaden value coverage.

## Dependence and Solver Knobs

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--isldep` | Compatible no-op | Pluto uses ISL dependence analysis by default. | Already acceptable. | Keep as no-op or pass-through. |
| `--islsolve` | Compatible no-op | Pluto uses ISL ILP solving by default. | Already acceptable. | Keep as no-op or pass-through. |
| `--candldep` | Supported conditionally | Candl is Pluto's alternate dependence tester. The old abort was a Pluto importer bug, not a PolOpt validator problem: `deps_read` missed `break`s when mapping Candl dependence types and did not handle `OSL_DEPENDENCE_RAW_SCALPRIV`. The current Pluto checkout has this fix and passes a dependent Candl smoke probe. | Yes, as oracle tuning. | Keep the runtime smoke probe. Pass `--candldep` to Pluto only when the selected binary does not abort, reject `--isldep --candldep`, and reject `--lastwriter --candldep` to match Pluto's own rule. |
| `--pipsolve` | Supported as oracle tuning | Solver selection changes Pluto's internal ILP solving path. It does not bypass PolOpt validation. | Already supported for checked routes whose produced schedule validates. | Broaden effect fixtures. |
| `--lastwriter` | Supported as oracle tuning | Native compatibility mode appends it to Pluto scheduler calls; `matmul.loop` demonstrates a schedule/codegen difference from the default dependence mode. | Already supported for checked routes whose produced schedule validates. | Broaden fixtures and reject unsafe combinations such as Candl if exposed later. |
| `--nolastwriter` | Supported as oracle tuning | This is Pluto's transitive-dependence mode and the current default. The driver now accepts it explicitly and rejects `--lastwriter --nolastwriter`. | Already supported. | Add effect-oriented checks only if a case makes the explicit flag differ from another normalized ordering. |
| `--isldepaccesswise`, `--isldepstmtwise`, `--isldepcoalesce` | Supported as oracle tuning | These tune ISL dependence extraction granularity/coalescing. Direct Pluto tests returned schedules on `matmul.c`, `fusion1.c`, and `nodep.c`; PolOpt still validates the resulting schedule. | Already supported for checked routes whose produced schedule validates. | Broaden effect fixtures and document any Pluto warnings, such as the ISL context warning seen with statement-wise extraction. |
| `--scalpriv` | Conservative support with `--candldep` | Scalar privatization is a Candl-only dependence-pruning mode. Without `--candldep`, Pluto still prints `compute_deps (isl)` and the flag is inert, so PolOpt rejects bare `--scalpriv`. With `--candldep`, PolOpt passes the flag to Pluto but still validates the produced schedule under the original scalar storage semantics. | Partly. This supports Candl scalar-privatization as oracle tuning only when no scalar storage rewrite is needed. | For full support, add a checked scalar-privatization route or validator/codegen condition that materializes private scalar storage. |

These flags do not need to be trusted for correctness if `polopt` validates the output schedule. The main risks are representation gaps and untested schedule shapes.

Effect-oriented search over the current `.loop` fixtures did not find a stable output-shape difference for `--candldep`, `--pipsolve`, `--isldepaccesswise`, `--isldepstmtwise`, or `--isldepcoalesce` after filtering out Pluto warnings and assertion text. These flags remain covered by pass-through and validation tests. Their remaining test TODO is to construct dependence-sensitive fixtures where the alternate dependence engine or granularity changes the schedule without relying on stderr differences.

`--candldep` should not be deleted from Pluto in this fork. It is still exposed by `tool/main.cpp`, it is mutually exclusive with `--isldep`, and it is the only Pluto path that makes `--scalpriv` meaningful. The abort was caused by two local importer omissions in `tool/osl_pluto.c`, not by an intentionally deprecated code path. Keeping it is useful because it lets PolOpt validate schedules produced by both Pluto dependence engines.

`--lastwriter` in Pluto means "remove transitive dependences by keeping the last conflicting access" for RAW/WAW and related flow computations. In `lib/program.cpp`, the false case computes dependences from any earlier conflicting access. The true case uses `isl_union_map_compute_flow` to keep the last writer or last read where appropriate. This can expose more scheduling freedom because fewer transitive dependences constrain the affine scheduler, but the produced schedule is still rechecked by PolOpt. Pluto rejects `--lastwriter --candldep`, so PolOpt rejects the same combination.

Scalar privatization means replacing a reused scalar storage location with logically separate private instances so that dependences through that scalar do not serialize otherwise independent iterations. Candl implements it by finding scalar variables whose def-use chain is dominated within a loop level and then pruning loop-carried dependences on those scalars. The key source path is `candl/source/dependence.c`: `candl_dependence_analyze_scalars` records `(scalar, loop)` pairs, and `candl_dependence_prune_with_privatization` removes or rewrites loop-carried scalar dependences, sometimes marking residual RAW dependences as `OSL_DEPENDENCE_RAW_SCALPRIV`.

That is not just a solver knob if the final schedule relies on each iteration having a private scalar instance. The current implementation therefore uses a conservative rule: `--scalpriv` must be paired with `--candldep`, and the resulting schedule is still checked against the original scalar storage semantics. The full Coq TODO is a scalar-private post pass over the loop IR: identify loop-local scalar temporaries, rename them to per-iteration storage or local declarations, prove semantic preservation under the privatization precondition, and then allow schedules that require the storage rewrite.

## Tiling Controls

| Pluto flag or feature | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--tile` | Supported on default full route | Current default is tiled. | Already supported. | Keep explicit compatibility. |
| `--notile` | Supported | Affine-only route exists. | Already supported. | Keep. |
| `--second-level-tile` | Supported on sequential full tiled route, including the ISS route | Existing validator route supports it, and `second-level-iss` now checks the focused ISS combination. | Already supported for ordinary and ISS routes. | Keep and extend tests. |
| `--intratileopt` | Supported as oracle tuning on tiled routes | Native compatibility mode treats it as an explicit alternative to `--nointratileopt`; it is appended to Pluto scheduler calls and validated by the existing phase split. | Already supported for checked routes whose produced tile witness validates. | Broaden fixtures and interactions with diamond/second-level routes. |
| `--nointratileopt` | Compatible no-op | Current checked recipes disable this Pluto rewrite unless `--intratileopt` is explicitly selected. | Already acceptable. | Keep as no-op with explanation and reject contradictory use with `--intratileopt`. |
| `--determine-tile-size` | Supported as oracle tuning on tiled routes | Native compatibility mode appends it to Pluto scheduler calls; `matmul.loop` demonstrates a final loop difference from fixed-size tiling. | Already supported for checked routes whose produced tile witness validates. | Broaden fixtures and test interactions with diamond/second-level routes. |
| `--cache-size`, `--data-element-size` | Supported with `--determine-tile-size` on tiled routes | Native compatibility mode parses positive integer values, appends them to Pluto scheduler calls, and rejects them when `--determine-tile-size` or a tiled route is absent. | Already supported for checked routes whose produced tile witness validates. | Broaden value choices and non-matmul fixtures. |
| `tile.sizes`, `--tile-sizes-file FILE` | Supported as Pluto legacy implicit file and explicit PolOpt compatibility input | Pluto reads this file from the working directory and uses its positive integers as first-level tile sizes. With `--second-level-tile`, later integers are second:first tile-size ratios. PolOpt can now install that file explicitly for the Pluto oracle call and remove it afterward. The checked tiling validator rechecks the produced tile-size witness. | native compat `optimizer-implicit-tile-sizes-file`, `optimizer-explicit-tile-sizes-file` | Prefer the explicit file option in artifact scripts. |
| `--ft`, `--lt` | Supported together on tiled routes | Pluto's first/last tiled hyperplane levels are passed through as non-negative values. The driver rejects one-sided or descending ranges. | Already supported for checked routes whose produced tiling witness validates. | Broaden effect fixtures and add out-of-range rejection tests because some valid-looking values trigger Pluto tiling assertions on small programs. |
| bare `--identity` | Unsupported in Pluto-compatible mode | Current Pluto keeps tiling enabled by default, while `polopt --identity` means no tiling. | Surface gap. | Keep requiring either `--identity --notile` or `--identity --tile`. |
| `--identity --tile --iss` | Supported narrow | A Coq route composes checked ISS complete-cut validation with checked identity tiling over the split program. | Already supported; current positive fixture shows tiling under `--iss` but not an ISS-sensitive extra effect. | Construct a fixture where ISS uniquely enables identity tiling, if Pluto has such a case. |
| `--identity --tile` with diamond/second-level composition | Unsupported composition | Parallel composition is now supported by validating identity tiling first and then running checked parallel codegen. Diamond and second-level forms still need a meaningful Pluto output shape and route-specific tests. | Composition gap. | Add each composition only when it can map to an existing extracted pass or a new Coq pass/theorem. |
| `--second-level-tile --parallel` | Supported | The phase-aligned route now extracts the second-level tiling artifact, validates it, then feeds the validated post-tiling program to the checked parallel validator/codegen path. | Already supported. | Broaden fixtures beyond `nodep` and `matmul-init`. |
| `--second-level-tile --parallel-current d` | Supported | Explicit-current parallel certification composes after the checked second-level tiling route. | Already supported. | Keep in second-level suite. |

Tile size control is likely easy from a proof perspective if the validator already proves tiling for arbitrary positive sizes. Partial tiling still needs broader effect fixtures, and mixed identity+tiling compositions need route-specific theorem coverage. A direct `--identity --tile --second-level-tile` experiment over 458 current `.loop` files found no positive second-level effect case: the route could be made to execute, but it fell back to identity or ordinary identity tiling. It therefore remains rejected until a route produces a validated second-level shape rather than merely accepting the flags.

## Parallel Controls

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--parallel`, `--parallelize` | Supported for one Pluto-hinted parallel loop by default | Current route validates one loop and emits checked parallel code. | Already supported. | Keep. |
| `--noparallel` | Supported as route control/no-op | Sequential routes use it. | Already supported. | Keep. |
| `--innerpar` | Compatible no-op | Current checked `--parallel` tiled recipe already keeps a canonical inner-parallel style. | Already acceptable. | Keep explanatory note. |
| `--multipar` | Supported on checked `--parallel` routes, up to two certified current dimensions | The driver passes the flag to Pluto, parses all OpenScop parallel loop hints, then lets the extracted validator filter certifiable dimensions before calling the extracted multi-cert parallel codegen route. The cap of two matches Pluto's current OpenMP pragma extraction. | Already supported for ordinary, second-level, and diamond parallel routes. | Broaden fixtures and add strict-mode checks. |
| `--forceparallel` | Supported pass-through/no-effect compatibility flag | Current Pluto source accepts the value but has no effective use site. | Already accepted as surface compatibility. | Keep explaining that no optimization effect is expected in the pinned Pluto source. |
| `--parallel-current d` | Supported as `polopt` extension, not a Pluto flag | Explicit checked parallel dimension. | Already supported. | Keep separate from Pluto compatibility mode. |
| `--parallel --parallel-strict` | Supported as `polopt` extension | Requires certified parallel loop to match Pluto hint. | Already supported. | Keep. |
| `--identity --tile --parallel`, `--identity --tile --parallel --multipar` | Supported narrow | The route validates ordinary identity tiling and then uses checked one- or two-dimension parallel codegen over the validated current-space program. The theorem-facing explicit-current entry is exposed as native `--identity-tiled --parallel-current d`, because `--parallel-current` is not a Pluto flag. | New positive fixtures show tiling plus `parallel for` effects; explicit-current route has `Opt_parallel_current_identity_tiled_result_correct`; parallel-current suite includes `identity-tiled-current-combined-effect`. | Broaden fixtures. |

The remaining `--multipar` work is no longer a route-closure gap for the main checked surface. The residual scope is broader regression coverage and any future attempt to go beyond Pluto's current two-pragma OpenMP extraction behavior.

## Diamond Tiling and Diamond Combinations

`--diamond-tile` and `--full-diamond-tile` are no longer single-route support.
The current native compatibility suite covers sequential, ISS, second-level,
parallel, and multipar compositions over the phase-aligned diamond route. The
remaining work is breadth of fixtures and output polish, not route closure.

| Combination | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--diamond-tile` | Supported | Phase-aligned route validates before -> mid affine, mid -> posttile tiling, and posttile -> after affine. | Already supported. | Keep suite coverage. |
| `--full-diamond-tile` | Supported | Same checked route with stronger Pluto producer mode. | Already supported. | Add more full-diamond cases beyond smoke. |
| `--diamond-tile --parallel` | Supported narrow | Diamond validation composes with the checked Pluto-hinted parallel route. | Already supported for current fixtures. | Broaden OpenMP/codegen fixtures and keep strict-mode checks separate. |
| `--diamond-tile --multipar` | Supported narrow | The diamond route can feed candidate current dimensions into checked multi-cert parallel codegen. | Already supported for current fixtures. | Broaden beyond the current batch fixtures. |
| `--diamond-tile --parallel-current d` | Supported as native PolOpt extension | Explicit-current certification composes after diamond validation. | Already supported outside the Pluto flag surface. | Keep as a theorem-facing entry point. |
| `--diamond-tile --iss` | Supported narrow | ISS bridge validation composes before the diamond affine and tiling phases. | Already supported for current fixtures. | Add broader ISS fixtures beyond the current stencil-like cases. |
| `--diamond-tile --second-level-tile` | Supported narrow | Second-level tiling witness extraction is enabled inside the same diamond phase route. | Already supported for current fixtures. | Add effect fixtures for more schedule shapes. |
| `--diamond-tile --notile` | Unsupported | Pluto itself disables diamond when tiling is off. | Correct rejection. | Keep rejecting. |
| `--diamond-tile --identity` | Unsupported | Diamond requires Pluto scheduling and tiling phase. | Correct rejection for current route. | Only reconsider if an identity-diamond route has a clear Pluto meaning and tests. |

The diamond gap is not "diamond is unsupported". The remaining gap is stronger
coverage: more fixtures for full-diamond, second-level, ISS, and multipar
interactions, plus any cleanup needed for singleton-loop raw-codegen fallback
output.

## Stale or Current-Pluto-Unsupported Flags

These flags appear in old scripts, examples, or code fields, but the current Pluto binary rejects them.

| Flag | Current state | Action |
|---|---|---|
| `--multipipe` | Pluto rejects. | Treat as stale. Do not support. |
| `--lbtile` | Pluto rejects. | Treat as stale. Do not support. |
| `--sched` | Pluto rejects. | Treat as stale. Do not support. |
| `--variables_not_global` | Pluto rejects. | Treat as stale. Do not support. |
| `--dump-iss-bridge` | Baseline `/pluto` binary rejects it; the ISS-export Pluto fork parses it as debug/export surface. | Keep it outside optimizer compatibility. If needed, expose it only as explicit ISS debug tooling. |
| `--output` | Pluto rejects; current binary uses `-o`. | Use `polopt` output options, not Pluto compatibility. |
| `--unroll` | Accepted only as a getopt abbreviation for `--unrolljam`. | Do not expose as a separate capability. |

These are not `polopt` deficiencies.

## Implementation Plan

The first artifact step is now in place: `./polopt --pluto-compat` is the
native Pluto-style filtered entry point, implemented in the OCaml driver and
tested by `make test-pluto-compat-suite`. The supported surface now includes
core affine/fusion knobs, partial tiling controls, parallel, multipar, and vector routes,
diamond compositions, conditional LP/DFP-family flags, and conditional Candl
dependence testing.

1. Keep a capability table in code.
   - Each entry should have status, reason, and route mapping.
   - Rejection messages should match tests.

2. Add remaining route-level surface gaps.
   - bare `--identity` policy remains explicit: require `--identity --notile`
     or `--identity --tile`
   - mixed `--identity --tile` compositions with diamond or second-level
     tiling
   - an ISS-sensitive `--identity --tile --iss` fixture, if one exists
   - broader tests for explicit `--tile-sizes-file`, `--fusion-structure`, and
     `--precut-file` beyond the current regression fixtures

3. Treat semantic extensions as separate projects.
   - unroll-jam
   - vector pragmas or vector loop annotations
   - unbounded multipar/nested OpenMP beyond Pluto's current two-pragma extraction behavior
   - scalar privatization, because it can change the required scalar storage discipline

4. Keep stale flags rejected.
   - The rejection should say "current Pluto does not support this flag", not "polopt does not support this optimization".

## Testing Plan

The executable compatibility suite should grow into the regression test for this interface.

Current smoke command:

```bash
make test-pluto-compat-suite
make test-vector-current-suite
```

Current result with the pinned GLPK-enabled Pluto baseline:

```text
[pluto-compat-suite] OK (76 checks)
```

The suite should add one test per supported flag group and one test per rejection class. For every new supported flag, the acceptance criterion should be:

1. Pluto accepts the same flag combination on a comparable case.
2. `polopt` accepts the flag combination.
3. `polopt` output validates through the checked route.
4. The test confirms that the flag is not silently ignored when it should change the schedule.

For rejected flags, the acceptance criterion is a stable, specific reason. A generic "unsupported" message is not enough.

## Short Summary

The current `polopt` surface already covers the core checked subset: affine scheduling, ordinary tiling, Pluto `tile.sizes` tile-size control via implicit and explicit `--tile-sizes-file` input, Pluto `.fst` fusion-structure control via implicit and explicit `--fusion-structure` input, Pluto `.precut` partial-transformation control via implicit and explicit `--precut-file` input, identity tiling with checked ISS and Pluto-hinted parallel/multipar composition, second-level tiling, ISS, one-loop parallelization, checked vector annotation for Pluto `--prevector`, `--multipar` parallelization up to two certified dimensions, sequential diamond tiling, full-diamond mode, conditional Candl dependence testing, conservative `--candldep --scalpriv` pass-through, and LP/DFP-family pass-through on the pinned GLPK-enabled Pluto baseline.

Most missing Pluto optimizer knobs are now surface gaps or composition gaps. The clearest proof/semantic gaps are `--unrolljam`, vector/codegen effects, unbounded multipar beyond Pluto's current extraction model, and full scalar privatization when the accepted schedule needs private scalar storage. Frontend and backend flags should remain outside the optimizer compatibility surface.
