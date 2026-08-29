# Pluto-Polopt Compatibility Surface

Date: 2026-07-21

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
- Current Pluto baseline builds:
  - ordinary `/pluto` HEAD: `8c43c210c9c08c5958198f22db4b54000380925e`
  - bug-only `/opt/polcert/pluto-buggy` HEAD:
    `6f43860b6c4cddeeca09189bf3073f05b78b14a5`
  - configured with `./configure --enable-glpk --with-glpk-prefix=/usr`
  - `pluto --help` advertises `--glpk`, `--lp`, `--dfp`, and `--typedfuse`
  - ordinary driver and compatibility tests use only the fixed checkout;
    executable bug witnesses explicitly select the historical checkout
- Candl probe:
  - original `/pluto/tool/pluto --candldep` aborted on `matmul.c`, `fusion1.c`, and Candl's `scalpriv.c`
  - root cause: `tool/osl_pluto.c:deps_read` converted Candl dependence types with fall-through, so recognized Candl dependences became `PLUTO_DEP_UNDEFINED`
  - fix applied in the Pluto checkout: add `break` statements and import `OSL_DEPENDENCE_RAW_SCALPRIV` as a Pluto RAW dependence
  - after rebuilding `/pluto`, `--candldep` and `--candldep --scalpriv` return successfully on `matmul.c`, `fusion1.c`, `nodep.c`, and Candl's `scalpriv.c`
- `--ufactor` probe:
  - direct Pluto on extracted `matmul.loop` shows `--ufactor=3` changes the automatic tile-size model from a 64-sized tile to a 63-sized tile under `--determine-tile-size --cache-size=32768 --data-element-size=8 --nounrolljam`
  - without `--determine-tile-size`, the same flag is accepted with checked `--unrolljam`; constant-bound loops are fully unrolled and variable-bound sequential loops use block/remainder unroll plus per-candidate same-bound sibling-loop jam validation
- `--unrolljam` probe:
  - `tools/artifact/explore_codegen_gaps.py` runs direct Pluto on extracted `matmul.loop` with `--unrolljam --ufactor=4` and `--nounrolljam`
  - the two Pluto runs produce identical `.afterscheduling.scop` files but different generated C, with `+=4` unrolled loops and remainder loops in the `--unrolljam` output
  - `tools/artifact/explore_unrolljam_effect_corpus.py` generalizes this into a direct-Pluto effect corpus: in the default 11-fixture set, native Pluto shows 6 clean codegen-only unroll-jam effects and the affine-validated PolOpt `--notile --unrolljam` route covers all 6 structurally
  - the checked side rejects the measurement if it observes any tiling-validation route, so the 6/6 result measures only the Loop-level unroll-jam path and cannot be satisfied by a tiling path
  - the same corpus now records 0 fixtures where native Pluto shows no clean C change while PolOpt still applies an additional checked block/jam effect under the default selector
  - `LoopJamLower` now exposes `checked_unrolljam_loop_with_plan`: an untrusted `list unrolljam_candidate` selects candidate depth/path pairs, and the extracted checked pass still validates every selected block/jam transformation
  - `POLCERT_UNROLLJAM_POLICY=none` is a regression hook showing that the selector can suppress all unroll-jam effects without rejecting the pipeline; the normal driver uses a Pluto-profitability-compatible selector, while `POLCERT_UNROLLJAM_POLICY=checked-all-depths` attempts every discovered depth in targeted tests
  - native `polopt --pluto-compat --unrolljam` now accepts checked constant-bound full unrolling through `LoopUnroll.const_unroll_correct`
  - variable-bound cases now accept through `LoopUnroll.block_unroll_correct`, which emits a checked block loop with repeated factor offsets plus a residual remainder loop, followed by verified cleanup
  - end-to-end C now includes `unrolljam_block_variable`, a variable-bound 2D integer kernel that checks block markers, compiles both baseline and optimized C, and compares exact output
  - per-candidate same-bound sibling-loop jam is implemented under the extracted end-to-end endpoint: the local checker retains equal parameter/enclosing-iterator schedule coordinates and validates cross-body independence within each shared outer environment on the candidate's actual affine bounds; otherwise it retains the checked order-preserving block/remainder output
  - first-class stride loops remain a TODO: the current proof deliberately lowers the block route into ordinary unit-stride `Loop.Loop` plus affine index reconstruction, avoiding a public stride constructor that would affect every downstream pass
- Current `polopt` route inspection:
  - `syntax/SLoopRoute.ml`: route normalization and explicit rejections
  - `driver/Scheduler.ml`: actual Pluto flag recipes sent by `polopt`
- Executed native compatibility mode:
  - public entry: `./polopt --pluto-compat`
  - implementation: `syntax/SLoopCli.ml` and `syntax/SLoopRoute.ml`
  - `tools/polopt_flag_suites/run_pluto_compat_suite.py`
  - integrated GLPK-enabled Pluto baseline result after direct-band routing,
    multipar, default no-RAR coverage, and broader effect coverage:
    `189 / 189` active checks passed (`172` base declarations, with one
    solver-rejection case replaced and `18` GLPK/Candl capability cases added
    for the pinned artifact: `126` explicit-RAR, `11` default-no-RAR, `10`
    native, and `42` rejection/not-applicable checks)
  - the suite also checks Pluto's default-on `--prevector` mapping, stale-current-Pluto flag rejections, missing explicit control-file rejection, non-matmul explicit control-file effects, and cleanup of temporary `tile.sizes`, `.fst`, and `.precut` files after explicit control-file runs
- Flag-effect exploration:
  - `tools/artifact/explore_flag_effects.py` compares `polopt --pluto-compat --explain` optimized loops for paired Pluto-style flag sets and writes JSON or Markdown evidence
  - `--group lp-dfp` found non-matmul effects for DFP, typed fusion, and hybrid fusion, and the native suite now includes a `corcol.loop` DFP/delayed-cut effect against the GLPK baseline. No delayed-cut-only difference beyond ordinary DFP has been established yet over the searched fixture set
  - `--group dependence-solver --max-fixtures 30` found no stdout optimized-loop effect for `--pipsolve`, `--candldep`, `--isldepaccesswise`, `--isldepstmtwise`, or `--isldepcoalesce`
- Executed diamond validation suite:
  - `make test-diamond-tiling-suite`
  - result: 5 diamond-effect cases validated, 2 no-effect cases validated,
    1 fixed-Pluto final-schedule rejection matched exactly, and 11 unsupported
    Pluto frontend inputs rejected as expected
- Identity composition exploration:
  - `tools/artifact/explore_identity_compositions.py` now records identity second-level, identity diamond, and identity+ISS-sensitive searches
  - `--identity --tile --second-level-tile` and `--identity --tile --iss --second-level-tile` are now accepted through checked generic identity-tiling routes; the focused `fusion7` probe shows a PolOpt 256/32 second-level tile shape that differs from ordinary identity tiling
  - over 63 regression `.loop` fixtures, direct Pluto `--identity --tile --diamond-tile` produced the same C output as `--identity --tile`; no identity-diamond-specific output effect was found
  - over 63 regression `.loop` fixtures, `--identity --tile` and `--identity --tile --iss` both succeeded with identical optimized loops; no ISS-only or ISS-different identity-tiling fixture was found in that bounded corpus
- Historical v2 artifact smoke check:
  - `make artifact-check` passed the pre-direct-band proof report, capability
    matrix, codegen and route suites
  - this result does not cover the direct-band integration; the final v3 image
    review must rerun the full claim suite and retain its raw result bundle
  - extended mode: `python3 tools/artifact/run_artifact_check.py --mode extended`
    adds the flag-effect exploration after the ordinary proof and suite checks

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

For tiling, `permutable-band` means that PolOpt's direct semantic analogue of
Pluto's fully permutable-band condition accepted a recognized layout. The
checker proves absence of decreasing conflicting pairs with certified
polyhedral emptiness queries. It does not call the whole affine-schedule
validator and does not certify Pluto's band detector or search procedure.
If the direct checker cannot establish the property, it reports `rejected`;
there is no alternate tiling-validation acceptance route, and the tiling
pipeline emits no optimized result.

| Pluto-style request | Current `polopt` behavior | Evidence |
|---|---|---|
| Default full tiled route | Runs checked affine scheduling, then the complete direct semantic permutable-band checker for ordinary tiling. | generated suite and native compat `ordinary-tiled` |
| `--notile` | Runs affine-only checked route. | native compat `affine-only` |
| `--identity --notile` | Runs no-Pluto identity extraction/codegen route. | existing CLI route |
| `--identity --tile` | Runs the checked identity-tiling route: identity extraction followed by Pluto's tile-only phase and the direct tiling validator/codegen chain. Program-wide semantic reconstruction covers the supported source-like and mixed-depth layouts. | native compat `identity-tiled`; `SBandTilingOpt.opt_identity_tiled`; `Opt_identity_tiled_band_correct` |
| `--identity --tile --parallel`, `--identity --tile --parallel --multipar` | Runs the same checked identity tiling boundary, then feeds Pluto's parallel loop hint(s) to the extracted checked parallel validator/codegen path. The explicit-current native route has a Coq theorem-facing entry as well. The positive fixture shows 32x32 identity tiling plus one or more certified `parallel for` annotations. | native compat `identity-tiled-parallel`, `identity-tiled-multipar`; `Opt_parallel_current_identity_tiled_result_correct`; extracted tiling and parallel validators/codegen |
| `--identity --tile --iss` | Runs checked ISS complete-cut recovery, then checked identity tiling over the split program. Current tests show the tiling effect remains available under `--iss`; the current `.loop` corpus did not contain a case where ISS uniquely enables identity tiling. | native compat `identity-tiled-iss`; `SBandTilingOpt.opt_identity_tiled_with_iss`; `Opt_identity_tiled_band_with_iss_correct` |
| `--identity --tile --second-level-tile` | Runs a checked generic identity-tiling route: identity extraction, Pluto tile-only second-level oracle, second-level tiling witness validation, and canonical PolOpt code generation. Recognized grouped/interleaved, source-like, and mixed-depth layouts use proved direct bridges. | native compat `identity-second-level` and `identity-second-level-matmul-init`; `Identity_tiling_generic_opt_prepared_correct`; identity-composition `fusion7` probe |
| `--identity --tile --iss --second-level-tile` | Runs checked ISS complete-cut recovery before the generic second-level identity-tiling route. The focused case shows the same 256/32 second-level shape under `--iss`. | native compat `identity-second-level-iss`; `identity_tiling_generic_opt_prepared_with_iss_correct` |
| `--iss` | Runs ISS + affine + tiling route when the input satisfies ISS shape constraints. | existing ISS suite |
| `--second-level-tile` | Runs the checked second-level tiling route on full tiled paths. Grouped and interleaved layouts satisfying the structural gate use the componentwise direct checker; the supported mixed-depth case uses the phase-aware direct bridge. | native compat `second-level`, `second-level-parallel`, and `second-level-parallel-matmul-init`; second-level suite |
| `--iss --second-level-tile` | Runs the sequential ISS + second-level route; the focused native compat case shows the expected two-level tile shape. | native compat `second-level-iss` |
| `--parallel` | Runs Pluto-hinted checked parallel route for one parallel loop. | native compat `parallel`; parallel tests |
| `--parallel-current d` | Runs the explicit padded-schedule-coordinate checked parallel route. The legacy option name is retained for compatibility. The native `--identity-tiled --parallel-current d` form exercises the extracted identity-tiling plus explicit-coordinate theorem route without pretending that `--parallel-current` is a Pluto flag. | parallel-current suite; `identity-tiled-current-combined-effect` |
| `--prevector`, `--vector` | Runs an innermost-only checked vector annotation route. PolOpt considers Pluto's vector hints, reuses the parallel/doall checker, and emits `vector for` only when the hinted loop is certifiable and structurally innermost. | native compat `prevector` and `default-prevector`; `checked_vector_annotated_codegen_correct_general`; vector-current suite |
| `--vector-current d` | Runs explicit padded-schedule-coordinate checked vector annotation and rejects `d` unless it is certifiable and structurally innermost. This is a native PolOpt theorem-facing route, not a Pluto flag. | vector-current suite |
| `--const-unroll` | Fully expands constant-bound loops on sequential output. On parallel output it expands only `SeqMode` loops and preserves every existing execution mode and origin tag. An explicit request fails when the selected output contains no eligible sequential loop. | native compat `native-const-unroll-constant-range`, `native-const-unroll-inside-parallel-current`, `native-const-unroll-inside-parallel-hint`, and `native-const-unroll-preserves-parallel-loop`; `ParallelLoop.const_unroll_semantics_refine`; `ExtractedPipelineCorrect.extracted_parallel_compile_with_const_unroll_correct` |
| `--unrolljam` | Runs the extracted checked Loop postpass. Sequential output accepts the general endpoint. Parallel output re-extracts supported results and obtains a fresh annotation certificate; it does not carry the old certificate across the rewrite. | native compat `const-unrolljam-constant-loop`, `block-unrolljam-ufactor-variable-loop`, `mixed-const-and-block-unrolljam`, `parallel-unrolljam-constant-range`, `reject-parallel-unrolljam-symbolic-reannotation`, and `unrolljam-context-bound-escape-rejected`; end-to-end C `const_unroll`, `unrolljam_block_variable`, and `unrolljam_dependent_guard`; `LoopJamBridge.checked_pair_refines_sound`; `ExtractedPipelineCorrect.extracted_sequential_compile_with_unrolljam_correct`; `ExtractedPipelineCorrect.extracted_parallel_after_unrolljam_correct` |
| `--diamond-tile` | Runs the sequential diamond phase-aligned route. Its tiling leg can report direct `permutable-band`; its separate final affine leg is checked by `validate_general`. | native compat `diamond`; diamond suite |
| `--full-diamond-tile` | Runs stronger diamond producer mode on the same checked route. The `jacobi-1d` case shows a route-level difference from non-diamond tiling; the batch fixture checks the same diamond-shaped output is accepted on a more complex stencil. | native compat `full-diamond` and `full-diamond-batch` |
| `--smartfuse` | Passed through to Pluto's checked scheduler oracle; this is also the default fusion policy in current recipes. | native compat `ordinary-tiled`; oracle flag note |
| `--nofuse` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-nofuse-affine`; differs from smartfuse baseline |
| `--maxfuse` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-maxfuse-affine`; differs from smartfuse baseline |
| `--nodepbound` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-nodepbound-affine`; differs from smartfuse baseline |
| `--per-cc-obj` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-per-cc-obj-affine`; differs from smartfuse baseline |
| `--flic`, `--fast-lin-ind-check` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-flic-affine` and `optimizer-fast-lin-ind-check-affine`; differ from smartfuse baseline |
| `--determine-tile-size` | Passed through to Pluto's checked scheduler oracle on tiled routes. | native compat `optimizer-determine-tile-size`; differs from fixed-size tiling baseline |
| `--cache-size <n>`, `--data-element-size <n>` | Passed through to Pluto's checked scheduler oracle when paired with `--determine-tile-size` on tiled routes. | native compat `optimizer-cache-size` and `optimizer-data-element-size`; differ from automatic tile-size baseline |
| `--ufactor <n>` with `--determine-tile-size` | Passed through as Pluto's tile-size-model rounding factor while `--nounrolljam` keeps unroll-jam disabled. | native compat `optimizer-ufactor-tile-model`; direct Pluto `matmul.loop` probe changes a tile size from 64 to 63 for `--ufactor=3` |
| `--intratileopt` | Selects the checked post-tiling affine route. PolOpt validates the pre-tiling schedule, the tiling mapping, and Pluto's final intra-tile affine rescheduling as separate transformations. | native compat intratile matrix: plain/ISS, one/two-level, identity/affine, parallel/vector, rectangular/diamond |
| `--lastwriter` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-lastwriter-affine`; differs from default dependence mode baseline |
| `--nolastwriter` | Passed through to Pluto's checked scheduler oracle and rejected if combined with `--lastwriter`. | native compat `optimizer-nolastwriter-affine` |
| `--candldep` | Conditionally passed through when the selected Pluto binary passes a dependent Candl smoke probe. The current `/pluto` baseline has the Candl importer fix. | direct Pluto Candl smoke checks; native compat `optimizer-candldep-affine`; rejects `--candldep --lastwriter` and `--isldep --candldep` |
| `--candldep --scalpriv` | Conservatively passed through to Pluto's checked scheduler oracle. PolOpt does not generate private scalar storage; it accepts only schedules and parallel hints that still validate under the original scalar storage semantics. | native compat `optimizer-candldep-scalpriv-affine` and `optimizer-candldep-scalpriv-parallel-conservative`; rejects bare `--scalpriv` |
| `--isldepaccesswise`, `--isldepstmtwise`, `--isldepcoalesce` | Passed through to Pluto's checked scheduler oracle. | native compat dependence-tuning checks; direct Pluto smoke checks on `matmul.c`, `fusion1.c`, and `nodep.c` |
| `--pipsolve` | Passed through to Pluto's checked scheduler oracle. | native compat `optimizer-pipsolve-affine`; direct Pluto smoke checks on `matmul.c`, `fusion1.c`, and `nodep.c` |
| `--coeff-bound <n>` | Passed through to Pluto's checked scheduler oracle as a positive integer value. | native compat `optimizer-coeff-bound-affine`; direct Pluto smoke checks |
| `--ft <n>`, `--lt <n>` | Passed through together as non-negative oracle controls, but PolOpt does not rely on them to restrict transformation scope. The pinned Pluto implementation uses them to change how many tile sizes it reads while still tiling the selected bands. PolOpt validates the actual output rather than claiming exact partial-level behavior. | native compat `partial-tiling-levels`; source audit of `lib/tile.c` |
| `--forceparallel <bitvec>` | Passed through as a non-negative value. The pinned Pluto source accepts it but has no effective use site. | native compat `optimizer-forceparallel-pass-through`; Pluto source grep |
| `--glpk`, `--lp`, `--dfp`, `--ilp`, `--lpcolor`, `--clusterscc`, `--typedfuse`, `--hybridfuse`, `--delayedcut` | Passed through on the pinned GLPK-enabled Pluto baseline, with a runtime rejection if an alternate Pluto binary lacks LP/DFP support. | native compat GLPK-family affine checks; DFP/typed/hybrid/delayedcut effect checks on non-matmul fixtures where available |
| `--rar` | Explicitly passed through to Pluto's checked scheduler oracle. Omission matches Pluto's default and leaves RAR relations disabled. | default/no-RAR and explicit-RAR automatic-affine regression |
| `--nointratileopt`, `--noprevector`, `--nounrolljam`, `--noparallel`, `--nodiamond-tile` | Accepted when they match the checked route's disabled Pluto-side effects. `--noprevector` disables vector annotation; omitting it keeps Pluto's default `--prevector` and selects the checked vector route. | native compat suite |

The current default `polopt` route is not "Pluto default". It intentionally uses phase-aligned recipes. For ordinary sequential optimization, it runs an affine-only Pluto phase with tiling and codegen effects disabled, then a tile-only Pluto phase with `--identity --tile`. With `--intratileopt`, PolOpt instead records Pluto's affine, post-tiling, and final schedule artifacts. It validates the first schedule with the affine validator, the second transformation with the permutable-band tiling validator, and the final intra-tile rescheduling with `validate_general`.

Within those phase-aligned recipes, options unrelated to phase isolation retain
Pluto's defaults. In particular, PolOpt does not add `--rar`; the flag affects
the oracle only when the user supplies it explicitly.

### RAR Regression Policy

Most scheduler-bearing tests predate this default change. They were originally
calibrated with RAR enabled: the legacy Pluto corpus supplies `--rar`
explicitly, while the old PolOpt scheduler recipes inserted it internally.
Those expectations are not silently reinterpreted as no-RAR expectations.

The test system now separates the two oracle policies:

- `test-polopt-loop-suite` exercises the current default no-RAR pipeline over
  all 62 generated Loop inputs. Its structural-change and tiling thresholds
  were rerun after the default changed.
- `test-pluto-compat-suite` retains the historical option/effect cases with
  explicit `--rar`. A suite-wide invariant rejects any historical successful
  non-native case that loses this flag. Its log labels them
  `oracle-policy=explicit-rar`.
- The same compatibility suite contains separately calibrated
  `default-no-rar-*` cases for affine scheduling, tiling, ISS, parallel and
  vector annotations, diamond tiling, and two-level tiling. Its log labels
  them `oracle-policy=default-no-rar`.

The two policies are not required to produce identical candidates. For
example, the no-RAR matmul vector route currently receives no vector hint and
therefore records a checked skip, while another no-RAR independent-loop case
does receive and apply a certified innermost hint. Both behaviors have explicit
effect contracts. Correctness never depends on RAR: every candidate is checked
after Pluto returns it.

Parser and unsupported-route rejection cases do not establish a scheduler
oracle policy, so the summary labels them `oracle-policy=not-applicable` rather
than inflating the no-RAR count.

For a corpus-level A/B comparison, run `make compare-rar-policy`. The script
runs identical checked sequential routes over all generated Loop inputs, with
`--rar` as the only changed oracle flag. It reports acceptance, final Loop
equality, tiling and annotation changes, per-side driver time, and optional
scheduled-OpenScop differences. Parallel and vector routes can be added with
repeated `--mode` arguments, and `--pipeline` selects affine-only or tiled
comparison. The source audit, literature correspondence, full-corpus result,
and executable spot checks are in
[the RAR policy study](pluto-rar-policy-study.md).

### Pluto Default Audit

The RAR change was checked against the other Pluto defaults at the pinned
source's `pluto_options_alloc` and command-line normalization. The resulting
policy is:

| Pluto setting | Pinned default | PolOpt treatment |
|---|---:|---|
| fusion | `smartfuse` | Same default; explicit fusion alternatives are forwarded. |
| RAR | disabled | Same default after this change; explicit `--rar` is forwarded. |
| inner parallelism | disabled | Same default; explicit `--innerpar` is forwarded to each applicable checked Pluto oracle phase. |
| dependence analysis | ISL, access-wise, no coalescing, no last-writer reduction | Same defaults; alternatives are forwarded and conflicting combinations are rejected. |
| schedule solver | ISL | `--islsolve` is an explicit no-op because it is already the default; `--pipsolve` and LP/DFP solver choices are forwarded. |
| tiling, intra-tile optimization, prevector, unroll-jam, parallelization, diamond tiling | enabled in various Pluto defaults | Deliberately not inherited wholesale. Compatibility mode requires the caller to select the corresponding checked phase or explicitly disable it. |
| debug, more-debug, silent | diagnostic only | Accepted as logging-only no-ops. |
| CLooG backtracking | enabled | `--nocloogbacktrack` is a no-op because PolOpt does not use Pluto's code generator. |

No other optimizer option that changes Pluto's scheduling candidate remains in
the compatibility driver's generic no-op set. Phase-changing defaults are
handled explicitly because they select different proved validators and
code-generation routes; this is separate from oracle-policy defaults such as
RAR, fusion, dependence analysis, and solver selection.

The bare Pluto flag `--identity` needs special care. In the current Pluto
source, tiling is enabled by default, so `--identity` can still reach the tiling
phase. The compatible `polopt` no-tiling identity route is therefore modeled as
`--identity --notile`. Plain sequential `--identity --tile` has its own
theorem-facing route: it exports the identity schedule, runs Pluto's tile-only
phase, and validates the tiling boundary before code generation. This route is
intentionally narrower than the default affine+tiling route. It tiles programs
whose source-order schedule yields a candidate accepted by the unified tiling
dispatcher; supported source-like layouts use semantic reconstruction. Programs that
need Pluto's affine scheduling first still belong to the default route.

The `--identity --tile --second-level-tile` and
`--identity --tile --iss --second-level-tile` forms use generic identity-tiling
routes so the checked output preserves Pluto's outer-first 256/32 second-level
shape. The `--identity --tile --parallel` route composes the checked tiling
boundary with the extracted checked parallel validator/codegen path.
`--multipar` uses the same verified compiler wrapper through a
list-of-dimensions config and certifies every accepted dimension in the
candidate list. The `--identity --tile --iss` form has the corresponding
theorem-facing composition with ISS split validation first. Current tests do
not claim an ISS-sensitive extra tiling effect.

The compatibility mode also requires callers to say how they want to handle Pluto defaults. A bare invocation is rejected. The caller must explicitly handle intratile optimization with `--nointratileopt` or `--intratileopt`, and unroll-jam with either `--nounrolljam` or explicit `--unrolljam`; must choose either `--noparallel` or `--parallel`; and must choose either `--nodiamond-tile` or a diamond route. For vectorization, Pluto's default-on `--prevector` now maps to PolOpt's checked vector route, while `--noprevector` disables that annotation.

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
| `--prevector` | Supported narrow | Pluto records vector loops as OpenScop loop directives. PolOpt parses directive bit `4`, then reuses the checked parallel/doall certificate to emit `vector for`. The driver considers only Pluto's innermost vector hints. If none is certifiable and structurally innermost, automatic mode retains the verified sequential producer; it does not scan non-innermost dimensions. | Already supported by the checked vector annotation route. | Add specialized vector checkers only if future semantics need fixed-width SIMD, reductions, or backend-specific pragmas. |
| `--noprevector` | Compatible no-op | Disables checked vector annotation. | Already acceptable. | Keep as no-op with explanation. |
| `--unrolljam` | Supported sequentially; narrow parallel composition | Pluto performs loop-body rewriting after codegen. PolOpt instead runs an extracted checked postpass: actual-domain affine validation retains equal parameter/enclosing-iterator coordinates and proves cross-body independence inside each shared outer environment, the certificate bridge establishes native trace permutability, and the contextual theorem covers recursive lowering. Parallel mode then re-extracts the transformed Loop and obtains a fresh identity-codegen parallel certificate; constant-range block unrolling exercises this route. Symbolic block/remainder bounds that introduce `Div`, `Max`, or `Min` are rejected by the current extractor, and vector combinations remain rejected. | Already supported for sequential output and affine-reextractable parallel results. | Add a metadata-preserving annotated theorem or proved piecewise-affine re-extraction to broaden the parallel subset and support vector output. |
| `--nounrolljam` | Compatible no-op | Current checked recipes already disable Pluto unroll-jam. | Already acceptable. | Keep as no-op with explanation. |
| `--ufactor` without `--determine-tile-size` | Supported with checked `--unrolljam` | With automatic tile-size selection absent, Pluto's general meaning is the unroll-jam factor. PolOpt records it as the block factor for `LoopUnroll.block_unroll_correct`; it is not passed to Pluto's scheduler oracle in this mode. | Supported for the checked route. | Broaden effect cases and keep exact Pluto codegen choices as non-trusted oracle behavior. |
| `--cloogsh`, `--cloogf`, `--cloogl` | Unsupported | These tune Cloog code generation, which `polopt` does not use as trusted output. | Not as optimizer flags. | Only expose equivalent `polopt` codegen knobs if needed. |
| `--nocloogbacktrack` | Compatible no-op in native compatibility mode | It only constrains Pluto/Cloog code generation, which `polopt` discards. Accepting it avoids rejecting a harmless disabling flag. | Already acceptable as no-op. | Keep the native note explicit so users do not infer Cloog output is validated. |
| `--codegen-context` | Unsupported | This shapes Pluto/Cloog generated bounds. `polopt` regenerates code itself. | Possible as a `polopt` codegen knob. | Add a checked codegen context option if the loop language needs it. |
| `--bee`, `--indent`, `-o` | Unsupported in native compatibility mode | These are backend/output concerns. | Possible under `polopt` names. | Add `polopt` output formatting/path options separately from optimizer compatibility. |

These are mostly backend features rather than missing scheduler optimizations. A direct Pluto probe on `matmul.loop` shows that `--prevector` adds an OpenScop `<loop>` extension with directive `4`; PolOpt imports that directive as a checked vector annotation. The unroll-jam probe is different: Pluto's after-scheduling OpenScop is byte-identical with and without `--unrolljam`, but the generated C contains unrolled loops, jammed statements, and remainder loops. The corpus records the corresponding PolOpt structures under `--notile` and verifies the generated programs experimentally. `LoopUnroll` proves constant and block/remainder unrolling; `LoopJamBridge` connects actual-domain affine validation to the native trace theorem; `LoopJamContext` proves recursive composition. The candidate plan is untrusted and affects only which checked local attempts run. `--ufactor` remains split between the automatic tile-size model and the Loop-level unroll-jam factor.

The vector path follows the checked parallel route: recover an innermost Pluto
vector hint, validate the doall precondition and innermost structure, and emit a
checked vector annotation. This is sound for Pluto-style prevectorization
because Pluto derives its vector marker from parallel-loop analysis.

The unroll path is separate. The extracted sequential theorem covers complete
unrolling of constant-bound loops, block/remainder unrolling for variable
bounds, and locally validated same-bound sibling-loop jam. The validator uses
the actual candidate bounds; candidates whose bounds are not affine-extractable
are rejected. The certificate bridge and contextual theorem carry accepted
pairs through every recursive Loop context, so both `--const-unroll` and
sequential `--unrolljam` belong to top-level verified endpoints.

The candidate depth/path plan is untrusted. `POLCERT_UNROLLJAM_POLICY=none`
exercises the same `--unrolljam` path with an empty selector and confirms that
the command succeeds without factor/remainder markers.
`POLCERT_UNROLLJAM_POLICY=checked-all-depths` attempts the broad candidate set.
First-class stride loops would be a separate extension to `Loop`; they
would affect substitution, cleanup, codegen, parallel/vector tag erasure,
extraction, and their preservation proofs. The disabling flags `--noprevector`
and `--nounrolljam` remain accepted because callers use them to disable Pluto's
default codegen-side behavior for checked routes.

## DFP and Typed Fusion

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--typedfuse` | Supported on the pinned baseline | The pinned Pluto baseline advertises GLPK/DFP support; the suite validates both the shifted `matmul.loop` case and a non-matmul `adi.loop` case where typed fusion collapses the skewed loop nest into direct `0..N` bands. | Already supported when the selected Pluto binary advertises GLPK or Gurobi. | Broaden beyond the current dense-kernel fixtures. |
| `--hybridfuse` | Supported on the pinned baseline | Same binary capability requirement as typed fusion; the suite validates the DFP-style `matmul.loop` case and the same non-matmul `adi.loop` effect. | Already supported when the selected Pluto binary advertises GLPK or Gurobi. | Broaden beyond the current dense-kernel fixtures. |
| `--delayedcut` | Supported on the pinned baseline | DFP-only option; the suite validates `--glpk --dfp --delayedcut` on the representative affine `matmul.loop` case and on `corcol.loop` against the GLPK baseline. The current evidence is a DFP/delayed-cut effect, not a delayed-cut-only effect beyond ordinary DFP. | Already supported when the selected Pluto binary advertises GLPK or Gurobi. | Keep searching for a delayed-cut-specific fixture outside the current input set or with a targeted DFP stress case. |
| `--dfp`, `--lp`, `--ilp`, `--lpcolor`, `--clusterscc` | Supported on the pinned baseline | The pinned Pluto baseline advertises these LP/DFP controls, and native compatibility tests validate representative affine cases. | Already supported when the selected Pluto binary advertises the option. | Keep runtime rejection for alternate Pluto binaries that lack LP/DFP support. |
| `--glpk` | Supported on the pinned baseline | The PolCert Dockerfile rebuilds Pluto with `--enable-glpk --with-glpk-prefix=/usr`; the checker requires `--glpk`, `--lp`, and `--dfp` in `pluto --help`. | Already supported when the selected Pluto binary advertises `--glpk`. | Treat as oracle solver selection; validator remains the correctness gate. |
| `--gurobi` | Conditional support | Not available in the current container. | Supported only if a selected Pluto binary advertises `--gurobi`. | Same as `--glpk`, but requires a Gurobi-enabled build. |

This category is now default artifact behavior for GLPK-backed Pluto. If DFP or typed fusion only changes which affine schedule Pluto finds, the existing affine validator is the central correctness check. The suite checks a visible schedule effect on `matmul.loop`: `--glpk`, `--glpk --ilp`, `--glpk --lp`, `--glpk --lpcolor`, and `--glpk --clusterscc` select the direct `M,N,K` loop order, while `--glpk --dfp`, `--typedfuse --glpk`, `--glpk --hybridfuse`, and `--glpk --dfp --delayedcut` produce the shifted DFP-style loop nest. It also checks non-matmul effects: `--glpk --dfp` changes statement placement on `corcol.loop`, `--typedfuse --glpk` plus `--glpk --hybridfuse` change the `adi.loop` nest to direct `0..N` bands, and `--glpk --dfp --delayedcut` changes `corcol.loop` against the GLPK baseline. The flag-effect tool found the DFP/typed/hybrid effects automatically. It also gives the current negative evidence for delayed cuts as a separate heuristic: no stdout optimized-loop difference from ordinary DFP over the 125 input fixtures in its default search set.

## Fusion and Scheduling Objective Knobs

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--nofuse` | Supported as oracle tuning | Native compatibility mode appends it to Pluto scheduler calls after the default recipe flags. | Already supported for checked routes whose produced schedule validates. | Keep effect tests; broaden beyond affine-only fusion fixtures. |
| `--maxfuse` | Supported as oracle tuning | Same pass-through mechanism as `--nofuse`. | Already supported for checked routes whose produced schedule validates. | Keep effect tests; broaden beyond affine-only fusion fixtures. |
| `--smartfuse` | Supported as oracle tuning/default | Current recipes use it by default, and explicit `--smartfuse` is preserved in the Pluto oracle flag stream. | Already supported. | Keep explicit acceptance and ordering behavior. |
| `--per-cc-obj` | Supported as oracle tuning | Native compatibility mode appends it to Pluto scheduler calls; `pca.loop` demonstrates a schedule/codegen difference from smartfuse baseline. | Already supported for checked routes whose produced schedule validates. | Broaden fixtures and check interactions with tiling/diamond routes. |
| `.fst`, `--fusion-structure FILE`, `--fst-file FILE` | Supported as Pluto legacy implicit file and explicit PolOpt compatibility input | Pluto reads `.fst` from the working directory and uses it to force a statement partition for fusion or distribution. PolOpt can now install that file explicitly for the Pluto oracle call and remove it afterward. The produced schedule is accepted only when the checked affine validator accepts it. | native compat `optimizer-implicit-fst-file`, `optimizer-explicit-fst-file`, `optimizer-explicit-fst-file-fusion2`; suite checks explicit-file cleanup | Prefer the explicit file option in artifact scripts. |
| `.precut`, `--precut-file FILE`, `--precut FILE` | Supported as Pluto legacy implicit file and explicit PolOpt compatibility input | Pluto reads `.precut` from the working directory and uses it as a partial transformation for Pluto to complete. PolOpt can now install that file explicitly for the Pluto oracle call and remove it afterward. The produced schedule is accepted only when the checked affine and tiling validators accept it. | native compat `optimizer-implicit-precut-file`, `optimizer-explicit-precut-file`, `optimizer-explicit-precut-file-fusion2`; suite checks explicit-file cleanup | Prefer the explicit file option in artifact scripts. |
| `skipdeps.txt` | Rejected when present implicitly | Pluto removes the named dependences from schedule-legality constraints. This changes the transformation contract outside the command line and can produce lexicographically illegal schedules. | native compat `reject-implicit-skipdeps-file` | Keep rejected; a future debug-only interface must still validate against the complete original dependence set. |
| `codegen.context` | Rejected when present implicitly | Pluto/Cloog can silently restrict the generated parameter domain from the working directory. PolOpt regenerates code for the original checked domain. | native compat `reject-implicit-codegen-context-file` | Keep rejected; add an explicit checked source-domain restriction only as a separate language feature. |
| `.linearized`, `.nonlinearized` | Rejected when either is present implicitly | When both exist, Pluto replaces statement bodies by substring matching without binding the files to the input or dependence analysis. Stale files can therefore decouple the scheduled accesses from the emitted body. | native compat `reject-implicit-linearized-file`, `reject-implicit-nonlinearized-file` | Keep rejected; any future linearization importer must be explicit and must rebuild accesses and dependences from the imported body. |
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
| `--scalpriv` | Conservative support with `--candldep` | Scalar privatization is a Candl-only dependence-pruning mode. Without `--candldep`, Pluto still prints `compute_deps (isl)` and the flag is inert, so PolOpt rejects bare `--scalpriv`. With `--candldep`, PolOpt passes the flag to Pluto but still validates the produced schedule and parallel hints under the original scalar storage semantics. | Partly. This supports Candl scalar-privatization as oracle tuning only when no scalar storage rewrite is needed. | For full support, add a checked scalar-privatization route or validator/codegen condition that materializes private scalar storage. |

These flags do not need to be trusted for correctness if `polopt` validates the output schedule. The main risks are representation gaps and untested schedule shapes.

Effect-oriented search over the first 30 input fixtures did not find a stdout optimized-loop difference for `--candldep`, `--pipsolve`, `--isldepaccesswise`, `--isldepstmtwise`, or `--isldepcoalesce`. The tool compares stdout only, so Pluto warnings such as the ISL context warning do not count as effects. These flags remain covered by pass-through and validation tests. Their remaining test TODO is to construct dependence-sensitive fixtures where the alternate dependence engine or granularity changes the schedule.

`--candldep` should not be deleted from Pluto in this fork. It is still exposed by `tool/main.cpp`, it is mutually exclusive with `--isldep`, and it is the only Pluto path that makes `--scalpriv` meaningful. The abort was caused by two local importer omissions in `tool/osl_pluto.c`, not by an intentionally deprecated code path. Keeping it is useful because it lets PolOpt validate schedules produced by both Pluto dependence engines.

`--lastwriter` in Pluto means "remove transitive dependences by keeping the last conflicting access" for RAW/WAW and related flow computations. In `lib/program.cpp`, the false case computes dependences from any earlier conflicting access. The true case uses `isl_union_map_compute_flow` to keep the last writer or last read where appropriate. This can expose more scheduling freedom because fewer transitive dependences constrain the affine scheduler, but the produced schedule is still rechecked by PolOpt. Pluto rejects `--lastwriter --candldep`, so PolOpt rejects the same combination.

Scalar privatization means replacing a reused scalar storage location with logically separate private instances so that dependences through that scalar do not serialize otherwise independent iterations. Candl implements it by finding scalar variables whose def-use chain is dominated within a loop level and then pruning loop-carried dependences on those scalars. The key source path is `candl/source/dependence.c`: `candl_dependence_analyze_scalars` records `(scalar, loop)` pairs, and `candl_dependence_prune_with_privatization` removes or rewrites loop-carried scalar dependences, sometimes marking residual RAW dependences as `OSL_DEPENDENCE_RAW_SCALPRIV`.

That is not just a solver knob if the final schedule relies on each iteration having a private scalar instance. The current implementation therefore uses a conservative rule: `--scalpriv` must be paired with `--candldep`, and the resulting schedule is still checked against the original scalar storage semantics. The compatibility suite now includes `optimizer-candldep-scalpriv-parallel-conservative` on `scalpriv.loop`: the requested Pluto-style parallel annotation is declined with a warning, leaving the checked sequential schedule and emitting no `parallel for`. The full Coq TODO is a scalar-private post pass over the loop IR: identify loop-local scalar temporaries, rename them to per-iteration storage or local declarations, prove semantic preservation under the privatization precondition, and then allow schedules or parallel hints that require the storage rewrite.

## Tiling Controls

| Pluto flag or feature | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--tile` | Supported on default full route | Current default is tiled. | Already supported. | Keep explicit compatibility. |
| `--notile` | Supported | Affine-only route exists. | Already supported. | Keep. |
| `--second-level-tile` | Supported on sequential full tiled route, including the ISS route | Existing validator route supports it, and `second-level-iss` now checks the focused ISS combination. | Already supported for ordinary and ISS routes. | Keep and extend tests. |
| `--intratileopt` | Supported checked route on tiled paths | Native compatibility mode selects a typed intra-tile policy. The scheduler emits affine, post-tiling, and final artifacts. PolOpt validates affine scheduling, the permutable-band tiling mapping, and the final affine rescheduling separately. | Supported for rectangular and diamond tiling, plain and ISS paths, one and two levels, identity tiling, and checked parallel/vector consumers when the produced candidate validates. | Keep the combination matrix and preserve fail-closed rejection for candidates outside the proved recognizers. |
| `--nointratileopt` | Compatible no-op | Current checked recipes disable this Pluto rewrite unless `--intratileopt` is explicitly selected. | Already acceptable. | Keep as no-op with explanation and reject contradictory use with `--intratileopt`. |
| `--determine-tile-size` | Supported as oracle tuning on tiled routes | Native compatibility mode appends it to Pluto scheduler calls; `matmul.loop` demonstrates a final loop difference from fixed-size tiling. | Already supported for checked routes whose produced tile witness validates. | Broaden fixtures and test interactions with diamond/second-level routes. |
| `--cache-size`, `--data-element-size` | Supported with `--determine-tile-size` on tiled routes | Native compatibility mode parses positive integer values, appends them to Pluto scheduler calls, and rejects them when `--determine-tile-size` or a tiled route is absent. | Already supported for checked routes whose produced tile witness validates. | Broaden value choices and non-matmul fixtures. |
| `--ufactor` | Supported with `--determine-tile-size` on tiled routes; supported as the checked `--unrolljam` block factor otherwise | Pluto's automatic tile-size model rounds candidate sizes to a multiple of `ufactor`, even when `--nounrolljam` disables the post-codegen unroll-jam transform. Native compatibility mode passes `--ufactor` to Pluto only in this tile-size-model context. With `--unrolljam` and no `--determine-tile-size`, it is not passed to the scheduler oracle and is used by the checked LoopUnroll and local jam post pass. | Already supported for checked tile-size routes and checked unroll-jam routes. | Broaden effect fixtures against direct Pluto output. |
| `tile.sizes`, `--tile-sizes-file FILE` | Supported as Pluto legacy implicit file and explicit PolOpt compatibility input | Pluto reads this file from the working directory and uses its positive integers as first-level tile sizes. With `--second-level-tile`, later integers are second:first tile-size ratios. PolOpt can now install that file explicitly for the Pluto oracle call and remove it afterward. The checked tiling validator rechecks the produced tile-size witness. | native compat `optimizer-implicit-tile-sizes-file`, `optimizer-explicit-tile-sizes-file`, `optimizer-explicit-tile-sizes-file-nodep`; suite checks explicit-file cleanup | Prefer the explicit file option in artifact scripts. |
| `--ft`, `--lt` | Supported together on tiled routes | Pluto's first/last tiled hyperplane levels are passed through as non-negative values. The driver rejects one-sided or descending ranges. | Already supported for checked routes whose produced tiling witness validates. | Broaden effect fixtures and add out-of-range rejection tests because some valid-looking values trigger Pluto tiling assertions on small programs. |
| bare `--identity` | Unsupported in Pluto-compatible mode | Current Pluto keeps tiling enabled by default, while `polopt --identity` means no tiling. | Surface gap. | Keep requiring either `--identity --notile` or `--identity --tile`. |
| `--identity --tile --iss` | Supported narrow | A Coq route composes checked ISS complete-cut validation with checked identity tiling over the split program. | Already supported; current positive fixture shows tiling under `--iss`. A bounded artifact search over 63 regression fixtures found no ISS-only or ISS-different identity-tiling case. | Revisit only if a new Pluto/input corpus exposes a distinct ISS-sensitive identity-tiling effect. |
| `--identity --tile --second-level-tile` | Supported narrow | A Coq route now exports the identity schedule, invokes Pluto's tile-only second-level oracle, validates the second-level boundary through the direct permutable-band dispatcher, and code-generates from the canonical after-tiling artifact. The focused `fusion7` case shows the expected 256/32 outer-first tile shape and differs from ordinary identity tiling. | Already supported for directly tileable identity bands; the ISS variant uses the same direct permutable-band route. | Broaden fixtures while preserving rejection for layouts outside the proved direct bridges. |
| `--identity --tile --diamond-tile` | Unsupported no-effect composition | Direct Pluto still emits phase dumps accepted by the four-phase validator on the focused `wavefront` probe, but corpus search over 63 regression `.loop` fixtures found the `--identity --tile --diamond-tile` C output identical to `--identity --tile`: without Pluto's affine/skew scheduling phase, diamond adds no route-specific output effect. | Correct rejection for now. | Only reconsider if an identity-diamond fixture shows a distinct diamond effect and maps to a theorem-facing route. |
| `--second-level-tile --parallel` | Supported | The phase-aligned route now extracts the second-level tiling artifact, validates it, then feeds the validated post-tiling program to the checked parallel validator/codegen path. | Already supported. | Broaden fixtures beyond `nodep` and `matmul-init`. |
| `--second-level-tile --parallel-current d` | Supported | Explicit schedule-coordinate parallel certification composes after the checked second-level tiling route. | Already supported. | Keep in second-level suite. |

Tile size control is likely easy from a proof perspective if the validator already proves tiling for arbitrary positive sizes. Partial tiling still needs broader effect fixtures, and mixed identity+tiling compositions need route-specific theorem coverage. The current identity-composition evidence is reproducible with `python3 tools/artifact/explore_identity_compositions.py --output-root /tmp/polcert-identity-compositions`: identity+second-level is now a supported narrow route with visible 256/32 output on `fusion7`, while identity+diamond remains rejected because Pluto's identity diamond output is not distinct from ordinary identity tiling across the 63-fixture regression corpus.

## Parallel Controls

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--parallel`, `--parallelize` | Supported for one Pluto-hinted parallel loop by default | Current route validates one loop and emits checked parallel code. | Already supported. | Keep. |
| `--noparallel` | Supported as route control/no-op | Sequential routes use it. | Already supported. | Keep. |
| `--innerpar` | Supported oracle control on checked tiled parallel routes | Pluto changes wavefront schedule construction when it is enabled. PolOpt forwards it to the phase-aligned Pluto calls, then independently validates the returned tiling and parallel hint. | Supported. | The static forwarding gate, the compatibility-route telemetry, and the executable `tiling-innerpar-satvec` producer regression jointly prevent silent no-op treatment. |
| `--multipar` | Supported on checked `--parallel` routes for every certified schedule coordinate in the candidate list | The driver passes the flag to Pluto, parses OpenScop parallel loop hints, builds a route-specific candidate list from Pluto hints and canonical scattering depth, and calls the extracted verified `RawParallelCurrentMany*` compiler config. The Coq route filters certifiable coordinates before checked multi-cert parallel codegen, so this means "all accepted coordinates" rather than "all requested coordinates". | Supported for ordinary, second-level, identity-tiled, diamond, and ISS-aware parallel routes through `compile_verified_correct` plus the `Opt_parallel_current_many*` route theorems. The regression suite includes a three-dimensional independent loop that emits `parallel for i0`, `parallel for i1`, and `parallel for i2`. | Broaden fixtures; strict-mode positive behavior is covered by hint-only multipar checks, and an all-hints-rejected strict fixture would further tighten the regression suite. |
| `--forceparallel` | Supported pass-through/no-effect compatibility flag | Current Pluto source accepts the value but has no effective use site. | Already accepted as surface compatibility. | Keep explaining that no optimization effect is expected in the pinned Pluto source. |
| `--parallel-current d` | Supported as `polopt` extension, not a Pluto flag | Explicit checked padded schedule coordinate; `current` is retained in the option name for compatibility. | Already supported. | Keep separate from Pluto compatibility mode. |
| `--parallel --parallel-strict` | Supported as `polopt` extension | Requires certified parallel loop to match Pluto hint. | Already supported. | Keep. |
| `--identity --tile --parallel`, `--identity --tile --parallel --multipar` | Supported narrow | The route validates ordinary identity tiling and then uses checked one- or multi-schedule-coordinate parallel codegen over the validated polyhedral program. The Pluto-compatible hinted route dispatches through the verified wrapper; the explicit-coordinate native route remains useful for targeted theorem-facing tests because `--parallel-current` is not a Pluto flag. | Positive fixtures show tiling plus `parallel for` effects; one-coordinate route has `Opt_parallel_current_identity_tiled_result_correct`; multipar route has `Opt_parallel_current_many_identity_tiled_correct`; parallel-current suite includes `identity-tiled-current-combined-effect`. | Broaden fixtures. |

The remaining `--multipar` work is no longer a route-closure gap for the main checked surface. The residual scope is broader regression coverage and any future runtime/backend interpretation beyond the current checked `ParallelLoop` annotations.

The multi-current driver passes every dimension in the finite candidate list
constructed for that route to the checked `RawParallelCurrentMany*` route. No
two-element truncation remains.

## Diamond Tiling and Diamond Combinations

`--diamond-tile` and `--full-diamond-tile` are no longer single-route support.
The current native compatibility suite covers sequential, ISS, second-level,
parallel, and multipar compositions over the phase-aligned diamond route. The
remaining work is breadth of fixtures and output polish, not route closure.

| Combination | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--diamond-tile` | Supported | The phase-aligned route validates before -> mid affine, mid -> posttile tiling, and posttile -> after affine. The tiling leg can use the direct common-band checker; the final leg is checked separately by `validate_general`. | Already supported. | Keep suite coverage. |
| `--full-diamond-tile` | Supported | Same checked route with stronger Pluto producer mode. | Already supported. | Add more full-diamond cases beyond smoke. |
| `--diamond-tile --parallel` | Supported narrow | Diamond validation composes with the checked Pluto-hinted parallel route. | Already supported for current fixtures. | Broaden OpenMP/codegen fixtures and keep strict-mode checks separate. |
| `--diamond-tile --multipar` / `--diamond-tile --iss --multipar` | Supported narrow | The diamond route feeds candidate schedule coordinates through the verified `RawParallelCurrentManyPostTilingAffine*` wrapper path into checked multi-cert parallel codegen, with the ISS variant routed through `RawParallelCurrentManyPostTilingAffineISS`. | Current fixtures pass; proof surface includes `Opt_parallel_current_many_post_tiling_affine_correct` and `Opt_parallel_current_many_post_tiling_affine_with_iss_correct`. | Broaden beyond the current batch fixtures; strict-mode positive hint-only behavior is covered. |
| `--diamond-tile --parallel-current d` | Supported as native PolOpt extension | Explicit schedule-coordinate certification composes after diamond validation. | Already supported outside the Pluto flag surface. | Keep as a theorem-facing entry point. |
| `--diamond-tile --iss` | Supported narrow | ISS bridge validation composes before the diamond affine and tiling phases. | Already supported for current fixtures. | Add broader ISS fixtures beyond the current stencil-like cases. |
| `--diamond-tile --second-level-tile` | Supported narrow | Second-level tiling witness extraction is enabled inside the same diamond phase route. | Already supported for current fixtures. | Add effect fixtures for more schedule shapes. |
| `--diamond-tile --notile` | Unsupported | Pluto itself disables diamond when tiling is off. | Correct rejection. | Keep rejecting. |
| `--diamond-tile --identity` | Unsupported | Diamond requires Pluto scheduling and tiling phase. | Correct rejection for current route. | Only reconsider if an identity-diamond route has a clear Pluto meaning and tests. |

The diamond gap is not "diamond is unsupported". The remaining gap is stronger
coverage: more fixtures for full-diamond, second-level, ISS, and multipar
interactions, plus any cleanup needed for singleton-loop raw-codegen output.

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
| `--unroll` | Pluto accepts it only as a getopt abbreviation for `--unrolljam`. | Reject and require explicit `--unrolljam`, so the checked unroll route is not selected accidentally. |

These are not `polopt` deficiencies.

## Implementation Plan

The first artifact step is now in place: `./polopt --pluto-compat` is the
native Pluto-style filtered entry point, implemented in the OCaml driver and
tested by `make test-pluto-compat-suite`. The supported surface now includes
core affine/fusion knobs, partial tiling controls, identity second-level tiling,
parallel, multipar, and vector routes, diamond compositions, conditional
LP/DFP-family flags, and conditional Candl dependence testing.

1. Keep a capability table in code.
   - Each entry should have status, reason, and route mapping.
   - Rejection messages should match tests.

2. Keep the route-level edge cases explicit.
   - bare `--identity` policy remains explicit: require `--identity --notile`
     or `--identity --tile`
   - `--identity --tile --diamond-tile` needs a distinct Pluto effect fixture
     before it should be accepted; the current artifact search found none over
     63 regression fixtures
   - an ISS-sensitive `--identity --tile --iss` fixture is not currently known;
     the artifact exploration checked 63 regression fixtures and found no
     ISS-only or ISS-different identity-tiling case
   - broader tests for explicit `--tile-sizes-file`, `--fusion-structure`, and
     `--precut-file` beyond the current regression fixtures are now present for
     `nodep` and `fusion2`; continue broadening if new control-file patterns are
     added

3. Treat semantic extensions as separate projects.
   - first-class Pluto-style unroll-jam peeling choices beyond the current
     local block/remainder policy
   - first-class positive-stride loops in `Loop` beyond the current lowering
     into ordinary unit-stride loops with affine index reconstruction
   - scalar privatization when the accepted schedule needs private scalar
     storage
   - runtime/backend policies for nested OpenMP beyond the current checked
     `ParallelLoop` annotation semantics

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
[pluto-compat-suite] OK (138 checks)
```

The suite should add one test per supported flag group and one test per rejection class. For every new supported flag, the acceptance criterion should be:

1. Pluto accepts the same flag combination on a comparable case.
2. `polopt` accepts the flag combination.
3. `polopt` output validates through the checked route.
4. The test confirms that the flag is not silently ignored when it should change the schedule.

For rejected flags, the acceptance criterion is a stable, specific reason. A generic "unsupported" message is not enough.

## Short Summary

The current `polopt` surface covers affine scheduling, ordinary and second-level tiling, ISS combinations, Pluto-hinted parallel and vector annotation, multi-coordinate parallelization, sequential diamond tiling, conditional Candl dependence testing, and the pinned Pluto solver controls. Sequential unroll-jam is included under an extracted end-to-end theorem. A narrow parallel composition revalidates constant-range results after the postpass; symbolic non-affine results and vector combinations remain explicitly rejected.

The default unroll-jam selector follows Pluto's temporal-reuse and
register-budget effect policy on the direct corpus, while
`checked-all-depths` is a functional stress path. First-class
positive-stride Loop IR would make stride syntax explicit but requires updating
every downstream Loop pass/proof, and full scalar privatization requires a
checked scalar-private storage rewrite before accepting schedules that depend on
privatized scalar instances. Frontend and backend flags should remain outside
the optimizer compatibility surface.
