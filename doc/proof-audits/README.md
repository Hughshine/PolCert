# Proof Audit Index

These audits support a source-level readability pass over the main PolCert
proof modules.  They separate four questions that are easy to conflate:

1. What theorem chain is active in the checked pipeline?
2. Which facts belong to the module that currently proves them?
3. Why is each long proof long, and can that cost be reduced without hiding the
   mathematical argument?
4. Which exported declarations are unused by this repository, without assuming
   that they are safe to remove for external clients?

The initial baseline is commit `9162178` on branch
`proof/readability-cleanup`.  Inventories remove comments and strings before
building declaration-level dependency graphs.  Qualified repository uses are
recorded separately from same-name textual matches.  Reachability is evidence
about the current repository, not an API deletion policy.

Some individual reports retain the original `/tmp` artifact names to document
how the audit was produced.  The durable declaration inventories and complete
long-proof reviews are copied under this directory; raw intermediate search
logs are not part of the repository.

The cross-module ownership matrix and staged dependency plan are in
[CONSOLIDATED_REFACTORING_PLAN.md](CONSOLIDATED_REFACTORING_PLAN.md).

## Completed audits

| Module | Declarations | Long proofs reviewed | Audit | Inventory |
|---|---:|---:|---|---|
| `src/Extractor.v` | 263 | 60 | [Extractor](EXTRACTOR_AUDIT.md) | [inventory](EXTRACTOR_DECLARATION_INVENTORY.md) |
| `src/PolyLang.v` | 401 | 37 | [PolyLang](POLYLANG_AUDIT.md) and [long proofs](POLYLANG_LONG_PROOFS.md) | [CSV](inventories/POLYLANG_DECLARATIONS.csv) |
| `src/PolyBase.v` | 108 | 15 | [PolyBase](POLYBASE_AUDIT.md) | [CSV](inventories/POLYBASE_DECLARATIONS.csv) |
| `src/AffineValidator.v` | 176 | 23 | [Affine validator](AFFINE_VALIDATOR_AUDIT.md) and [long proofs](AFFINE_VALIDATOR_LONG_PROOFS.md) | [CSV](inventories/AFFINE_VALIDATOR_DECLARATIONS.csv) |
| `src/TilingRelation.v` | 221 | 47 | [Tiling relation](TILING_RELATION_AUDIT.md) | [CSV](inventories/TILING_RELATION_DECLARATIONS.csv) |
| `src/TilingBoolChecker.v` | 25 | 2 | [Tiling structural checker](TILING_BOOL_CHECKER_AUDIT.md) | [CSV](inventories/TILING_BOOL_CHECKER_DECLARATIONS.csv) |
| `src/TilingBandScheduleValidator.v` | 818 | 114 | [Permutable-band validator](TILING_BAND_SCHEDULE_VALIDATOR_AUDIT.md) | [CSV](inventories/TILING_BAND_SCHEDULE_VALIDATOR_DECLARATIONS.csv) |
| `src/TilingBandMixedSecondValidator.v` | 51 | 8 | [Mixed second-level validator](TILING_BAND_MIXED_SECOND_VALIDATOR_AUDIT.md) | [CSV](inventories/TILING_BAND_MIXED_SECOND_VALIDATOR_DECLARATIONS.csv) |
| `src/TilingBandPhaseScalarValidator.v` | 51 | 7 | [Phase-scalar validator](TILING_BAND_PHASE_SCALAR_VALIDATOR_AUDIT.md) | [CSV](inventories/tiling-band-phase-scalar-declarations.csv) |
| `src/TilingBandDirectRuntime.v` | 18 | 5 | [Direct runtime](TILING_BAND_DIRECT_RUNTIME_AUDIT.md) | [CSV](inventories/tiling-band-direct-runtime-declarations.csv) |
| `src/TilingValidator.v` | 74 | 5 | [Tiling representation bridge](TILING_VALIDATOR_AUDIT.md) | [CSV](inventories/tiling-validator-declarations.csv) |
| Canonical tiling and ISS facade/witness group | 144 | 4 | [Validator facades](VALIDATOR_FACADES_AUDIT.md) | [CSV](inventories/validator-facades-declarations.csv) |
| `src/ISSRefinement.v` | 69 | 3 | [ISS refinement](ISS_REFINEMENT_AUDIT.md) | [CSV](inventories/ISS_REFINEMENT_DECLARATIONS.csv) |
| `src/ISSSemantics.v` | 28 | 3 | [ISS semantics](ISS_SEMANTICS_AUDIT.md) | [CSV](inventories/ISS_SEMANTICS_DECLARATIONS.csv) |
| `src/ISSCutSemantics.v` | 36 | 6 | [ISS cut semantics](ISS_CUT_SEMANTICS_AUDIT.md) | [CSV](inventories/ISS_CUT_SEMANTICS_DECLARATIONS.csv) |
| `src/ParallelValidator.v` | 68 | 2 | [Parallel validator](PARALLEL_VALIDATOR_AUDIT.md) | [CSV](inventories/PARALLEL_VALIDATOR_DECLARATIONS.csv) |
| `polygen/ParallelLoop.v` | 129 | 7 | [Parallel loop semantics](PARALLEL_LOOP_AUDIT.md) | [CSV](inventories/PARALLEL_LOOP_DECLARATIONS.csv) |
| `src/ParallelCodegen.v` | 90 | 1 | [Parallel code generation](PARALLEL_CODEGEN_AUDIT.md) | [CSV](inventories/PARALLEL_CODEGEN_DECLARATIONS.csv) |
| `src/PrepareCodegen.v` | 79 | 14 | [Code-generation preparation](PREPARE_CODEGEN_AUDIT.md) | [CSV](inventories/prepare-codegen-declarations.csv) |
| `polygen/CodeGen.v` | 13 | 1 | [Sequential code generator](CODEGEN_AUDIT.md) | [CSV](inventories/codegen-declarations.csv) |
| Shared owner libraries (`Misc`, `ListExt`, `Linalg*`, `InstanceListSema`) | 401 | 9 | [Canonical owners](CANONICAL_OWNER_LIBRARIES_AUDIT.md) | [inventories](inventories/) |
| Frontend and final facade group | 218 | 4 | [End-to-end facades](END_TO_END_FACADES_AUDIT.md) | [inventories](inventories/) |
| `driver/PolOptCorrect.v` | 12 | 1 | [Sequential driver](POL_OPT_CORRECT_AUDIT.md) | [CSV](inventories/POL_OPT_CORRECT_DECLARATIONS.csv) |
| `driver/PolOptBandTiling.v` | 64 | 9 | [Tiling driver](POL_OPT_BAND_TILING_AUDIT.md) | [CSV](inventories/POL_OPT_BAND_TILING_DECLARATIONS.csv) |
| `driver/ParallelPolOptCorrect.v` | 135 | 9 | [Parallel driver](PARALLEL_POLOPT_CORRECT_AUDIT.md) | [CSV](inventories/PARALLEL_POLOPT_CORRECT_DECLARATIONS.csv) |

"Long" means a proof span of at least 30 lines in the audited source.  Local
Ltac bodies and mutual proof groups are reviewed separately where the simple
span rule would miss them.  The table covers 3,692 declarations in 38 files
and individually reviews 396 long proofs; the inventories still classify every
short declaration rather than treating the length threshold as the audit
boundary.

## Immediate conclusion

Most large proofs fall into three categories:

- **Genuine semantic bridges.**  The Extractor reconstruction induction,
  TilingRelation erasure/reconstruction stages, and layout-specific tiling
  reversal arguments carry real mathematical content.  They need named stages
  and small witness packages, not opaque automation.
- **Repeated representation recovery.**  Tiling, ISS, and parallel validators
  repeatedly reconstruct two endpoints, list membership, indices, schedules,
  and witness fields.  Private one-point fact packages can remove the duplicate
  plumbing while leaving the order or injectivity argument visible.
- **Compatibility layers proved from scratch.**  Empty-prefix, fuel, older
  non-`_at`, compiled-view, and route wrapper theorems often repeat a stronger
  active theorem.  Preserve their public names and types, but turn their proof
  bodies into explicit wrappers.

The first Extractor cleanup applies that policy: it replaces 1,702 old source
lines with 142 lines of aliases, wrappers, and named structure, shrinking the
file from 10,125 to 8,565 lines without changing an existing public declaration
type.  The remaining large Extractor theorem is the actual structured semantic
reconstruction.  The same pass shrinks a duplicated TilingRelation bridge from
140 proof lines to a call to the stronger theorem immediately above it.

## Verification of the Applied Cleanup

The ordinary project proof and test path was used throughout:

- clean full `make depend && make -j2 proof` after the Extractor cleanup:
  739.80 s, passing;
- isolated final `TilingRelation.vo` rebuild: 3.21 s, followed by a complete
  dependent `make -j2 proof` rebuild: 613.55 s, passing;
- `make -j2 extraction`: 100.60 s, passing;
- default `make -j2 test`: all 62 Pluto cases passing;
- `test-extracted-zero-fallback`: all six rejection paths passing;
- `test-direct-only-tiling-routes`: all 20 cases passing with zero fallback.

## Resolved parallel correctness boundary

The complete theorem-path audit is
[PARALLEL_CERTIFICATE_SEMANTICS_GAP.md](PARALLEL_CERTIFICATE_SEMANTICS_GAP.md).
The concrete raw-codegen coordinate check is recorded separately in
[PARALLEL_COORDINATE_REPRODUCTION.md](PARALLEL_COORDINATE_REPRODUCTION.md).

The parallel audits identified a semantic connection that was absent at commit
`9162178`:

- `ParallelValidator.checked_parallelize_current_sound` proves the certified
  polyhedral dimension is pairwise permutable across loop iterations.
- `ParallelLoop.PTLoopPar` admits a trace only when that trace already carries
  an `interleave_safe` proof.
- `ParallelCodegen.checked_annotated_codegen_correct_general` proves correctness
  for executions admitted by this restricted semantics, but does not use
  `parallel_cert_sound`.
- The driver obtains the validator certificate but its correctness proof does
  not apply the certificate soundness theorem.

That finding is now historical on `artifact/verified-compilation-v9-candidate`.  The target
semantics admits arbitrary order-preserving interleavings; the validator
certifies padded schedule coordinates; codegen-origin theorems relate actual
generated points to source instances; and the checked endpoint uses the
certificate to construct an ordered proof companion for each actual execution.
The original audit remains available as evidence of the defect and its required
proof obligations.  The formerly unused `interleave_family` and
`family_ordered_permutable` definitions now form the generic first step; the
new trace-origin and pointwise-certificate theorems discharge the previously
missing program-specific obligations.

The final repair snapshot was rebuilt from a clean tree with
`make depend && make -j2 proof`: 882.05 seconds wall time, 1,437.12 seconds user
CPU, 42.48 seconds system CPU, and 10,005,640 KiB peak RSS.  This is the proof
reproduction cost; extraction, executable linking, and behavior suites are
separate artifact stages.

## Refactoring discipline

1. Preserve every existing public theorem name and type during local proof
   cleanup.
2. Add canonical facts to a dependency-lower owner, then keep old module paths
   as exact wrappers.
3. Compile the edited module and its direct facade after each family of changes.
4. Measure clean and incremental builds separately.  Most proposed physical
   splits are linear and improve invalidation scope rather than clean-build
   parallelism.
5. Do not delete a repository-unreachable exported declaration without a
   separate compatibility decision.
6. Keep the parallel semantic repair in its own commit and review it as a new
   theorem contribution.
