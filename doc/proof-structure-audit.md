# Proof Structure and CI Audit

This document records the proof-readability and build work performed on the
parallel-interleaving branch.  The objective was not to minimize source line
count mechanically.  It was to make proof ownership, semantic stages, and
failure evidence visible while removing duplicate and unreachable proof paths.

## Audit method

The audit used four passes.

1. Build a declaration and proof-span inventory for every project-owned Rocq
   file.  The current tree contains 248 `.v` files and about 207,000 source
   lines.  The final span inventory contains 405 proofs of at least 30 lines,
   206 of at least 50 lines, and 65 of at least 100 lines.
2. Find repository callers and entry-point reachability before deleting a
   declaration.  Public-looking but unreachable declarations were removed only
   when the branch had already made the corresponding compatibility decision.
3. Read every proof of at least 30 lines in the high-cost project modules and
   classify its length as semantic induction, representation transport,
   endpoint reconstruction, compatibility duplication, or tactic noise.
4. Compile after each proof family.  Public theorem statements were kept stable
   unless an unreachable API family was intentionally retired.

Global replacement of `eauto` was deliberately rejected.  Most of its uses are
small wrappers with tightly constrained goals.  Replacing them mechanically
would add noise without exposing more proof structure.  Goal-shape matching was
instead removed where it hid semantic evidence in a long proof.

## Changes made

### Common proof libraries

- Canonical list membership, `nth_error`, `Forall2`, `NoDup`, filter, and map
  transport facts were centralized in `Misc.v` and `ListExt.v`.
- Repeated vector negation, dot-product, coordinate selection, resize, and
  exact-column facts were centralized in `Linalg.v` and `LinalgExt.v`.
- `lex_compare_lt_trans` was rewritten from integer-constructor and positive
  comparison enumeration into a head/tail proof.  The new proof has exactly
  four mathematical cases: head/head strict, strict/equal, equal/strict, and
  equal/equal followed by the induction hypothesis.
- Selection-sort minimum reasoning now uses the existing totality,
  transitivity, and `ord_all` lemmas.  It no longer reclassifies the same
  pairwise comparisons by hand.
- Stable permutation proofs use explicit intermediate states and named
  `State.eq` composition.  Anonymous existential fillers and the final
  `Unshelve`/dummy-state cleanup were removed.

### Polyhedral language and instance semantics

- Generic nil/cons/app/singleton instance-list inversions and schedule-insensitive
  semantic transport were moved to their canonical semantic owner.
- PolyLang flattening, retiming, selection, and stable-permutation routes were
  consolidated around one general theorem per property.  Narrow variants are
  wrappers instead of independent inductions.
- Duplicate predecessor and non-prefix proof families were removed after caller
  analysis.  The remaining slice/prefix theorems are the active representation
  used by extraction and code generation.
- Fragile stable-permutation state construction and misleading unfold steps were
  replaced with explicit data-flow names.

### Extractor

The former monolithic `Extractor.v` was split by responsibility:

- `ExtractorFrontend.v` (1,506 lines): affine translation, extraction, and
  extraction invariants;
- `ExtractorFacts.v` (1,293 lines): flatten/slice/order facts;
- `ExtractorCorrect.v` (2,104 lines): semantic reconstruction and the final
  correctness chain;
- `Extractor.v` (10 lines): compatibility facade preserving `Extractor PolIRs`.

Consumers that need only definitions or flattening facts now import the narrow
layer.  This improves incremental rebuilds and makes the reader path explicit.

Inside the proofs:

- old fuel, empty-prefix, and length compatibility theorems became wrappers;
- unreachable predecessor/non-prefix routes and duplicate list facts were
  removed;
- dead local snapshots and unused destructured hypotheses were deleted;
- the live prefix mutual theorem remains a structural induction because it is
  the theorem that reconstructs instruction, guard, sequence, and loop
  semantics.

### Tiling

- TilingRelation now has one canonical tiled-point decomposition and one set of
  list/semantic transport facts.  Duplicated compiled/general predecessor
  routes were removed where no active caller remained.
- Pair-local ordinary and second-level reversal bridges share endpoint facts and
  the common semantic kernel.  Mixed and phase/scalar validators reuse those
  packages instead of rebuilding both endpoints.
- More than a dozen layers of unused TilingBand projection, compatibility, and
  validation endpoints were removed by repository reachability analysis.
- Remaining schedule/layout bridges use explicit structure, environment,
  witness, and ordering fields.  Broad `repeat match goal` decomposition and
  inversion-generated hypothesis numbers were removed.
- Phase/scalar component soundness and final reordering share named endpoint and
  tiled-shape packages.  The preserved-phase/layout part remains visible.
- TilingValidator's outer/internal record conversion is expressed as a named
  local isomorphism with membership, NoDup, Sorted, permutation, and semantic
  transports; the two flatten iff theorems are now short wrappers.

### Affine and ISS validation

- AffineValidator's duplicate PointWitness equality functions are compatibility
  wrappers over the canonical implementation.
- Access-pair soundness is checker-parametric.  Rational and integer direct-band
  theorems use the same WW/WR/RW non-collision proof instead of copying it.
- Paired flattening reuses one composed-pinstr length theorem rather than proving
  the same length equality in both directions.
- ParallelValidator pointwise soundness constructs a named single-point view and
  invokes one direction helper.  Source and extended point reconstruction is no
  longer duplicated for the two reversal directions.
- ISS child endpoint/sign recovery is shared across cover/disjointness proofs.
  The complete-cut injectivity proof now obtains each flattened endpoint through
  one named witness package.
- Dead ISS reverse-search and isolated payload facts were removed.  Generic
  combine/map facts now come from the common list library.

### Parallel semantics and code generation

- The target parallel-loop semantics remains raw, order-preserving interleaving.
  Safety is not a constructor premise.  A separate ordered-trace companion
  carries the certificate-derived family permutability used by refinement.
- Actual single- and multi-certificate traces share the multi-certificate proof.
  Root source-origin, sibling schedule separation, pointwise certificate
  soundness, and ordered-trace construction are separate named stages.
- Raw code-generation origin is separated from code-generation correctness.
  Inversion evidence for scans, guards, projections, source points, and trace
  families is explicitly named.
- Parallel codegen was split into:
  - `ParallelCodegenCore.v` (1,736 lines): executable/tag/origin machinery;
  - `ParallelCodegenCompatibility.v` (665 lines): generic legacy bridges;
  - `ParallelCodegenCorrect.v` (1,096 lines): certificate-backed endpoints;
  - `ParallelCodegen.v` (10 lines): compatibility facade.
- Singleton/full cleanup reflects a cleaned execution to the already certified
  pre-clean execution.  The executable gate checks exactly the intermediate
  trace-safety obligations needed by that reflection.
- Loop cleanup, unrolling, stride, jamming, and parallel trace proofs use named
  iteration/family evidence.  One additional constant-unroll branch now passes
  its already named iteration semantics directly.

### Drivers and end-to-end facades

- Frontend extraction/strengthening/reflection is represented by one local
  lifting theorem and reused by route-specific public wrappers.
- Alarm impossibility and accepted-tail correctness are named helpers; fallback
  branches remain explicit.
- Parallel single/multi result and alarm-free wrappers use polymorphic local
  lemmas rather than large goal-shape Ltac scripts.
- Exhaustive route coverage proofs remain exhaustive.  They were annotated by
  route family rather than compressed into opaque automation.

## Remaining long proofs

The following table covers every current proof family with a member of at least
100 lines.  `Keep` means the proof was read and its length is dominated by a
real semantic or representation stage.  `Factored` means endpoint duplication
or tactic noise was removed but the mathematical core remains.

| Owner | Long proofs and current disposition |
| --- | --- |
| TilingBandScheduleValidator | Seven reversal bridges (588-1,332 lines): **Factored/Keep**.  Shared endpoint and pair packages are in place; the remaining body proves ordinary, second-level, scalar-aware, and phase layout reconstruction.  Four schedule/component soundness groups (101-215 lines): **Factored/Keep**, with explicit checker fields and layout stages. |
| ExtractorCorrect | `core_sched_stmt_stmts_constrs_prefix_mutual` (671): **Keep**, the live instruction/guard/sequence/loop reconstruction induction.  Prefix-slice split/rebase/lower-bound proofs (100-142): **Factored/Keep**. |
| ExtractorFacts | Loop index/timestamp master (171), slice/filter extension (180), sorted three-way split (133): **Keep**; narrower variants are wrappers. |
| TilingBandPhaseScalarValidator | Same-class reversal (357): **Factored/Keep** preserved-phase and common-layout reasoning.  Component/final reorder proofs (129/146): **Factored** through endpoint and shape packages. |
| TilingBandMixedSecondValidator | Mixed and phase-separated reversals (251/269): **Factored/Keep**; obsolete ordinary route removed and active endpoints share Core facts. |
| TilingRelation | Whole-list source permutation (228), after flatten representation (167), point injection/semantic/nth/preimage bridges (103-152): **Keep**.  The whole-list theorem is a real reverse-list induction over three aligned lists; there is no lower whole-list theorem to wrap. |
| AffineValidator | Extended flatten expansion/transport (158/254), collision/permutability/checker soundness (107-128): **Factored/Keep**.  Paired length and access-direction duplication was removed. |
| PrepareCodegen | Semantic collection (203): **Keep**, a four-invariant induction producing semantics, Sorted, NoDup, and exact membership.  Final semantics correctness (162): **Factored/Keep**. |
| ISSCutSemantics | Complete-cut point injection (200): **Factored**, endpoint recovery is shared; sign/domain uniqueness remains. |
| ASTGen | `generate_loop_many_preserves_sem` (190): **Keep**, split/sort recursion plus scan-union/order proof; stage comments expose the proof route. |
| PolyBase | Less/greater polyhedron correctness (160/173) and zero bridge (101): **Keep**.  Signed-coordinate copy/paste was removed; the directional inductions remain. |
| ParallelCodegenCorrect | Actual ordered trace, root origin, and ordered semantics (120-148): **Factored/Keep**, now separated into three stages and shared by single/multi endpoints. |
| ParallelCodegenCore | Prepared event to source point (110): **Keep**, the functor-boundary representation bridge. |
| ParallelLoop | Substitution, cleanup, and ordered refinement mutual proofs (109-138): **Factored/Keep**; family transports are local helpers and arbitrary-interleaving reasoning remains explicit. |
| RawCodegenOrigin | Scan trace inversion (149): **Factored/Keep**, with equality/bounds scan evidence named. |
| SelectionSort | Stable selection permutation (112): **Keep**, the recursive algorithm invariant.  Minimum proof fell from 126 to 54 lines after reuse of totality/order lemmas. |
| PolyLang | Schedule elimination semantics (107): **Keep**, the canonical retiming route after duplicate routes were removed. |
| CState | Read-after-write non-aliasing (114): **Keep**.  The larger store-commutation proof was already reduced from roughly 1,000 lines to layered map/store lemmas. |

Proofs below 100 lines were also inventoried and reviewed by the same ownership
groups.  The dominant retained categories are syntax-directed correctness
inductions, two-direction representation iff proofs, and explicit checker-field
reflection.  Short compatibility wrappers were not expanded merely to remove
`eauto`.

## Goal-shape tactics retained after experimentation

Project-owned active code has only a small set of intentional target-shape
matches left:

- `LoopGen.v` has two matches that name the generated guard test hidden inside
  an expanded `make_guard` equality.  Repeating that term would make the proof
  less readable and more sensitive to generator changes.
- `ASTGen.v` has one match that names the transformed scan predicate and mapped
  program from a large dependent semantic goal before generalization.
- `LoopUnroll.v` retains two local matches inside the multi-branch constant
  expression enumeration.  Explicit constructor patterns were tried; they left
  unresolved focus branches because the surrounding `try solve` intentionally
  handles many expression constructor pairs.  One independent occurrence was
  removed successfully.
- `LoopJamNative.v` has one match pairing the evaluation-vector equality with
  the instruction-semantics evidence produced by a mutual induction.  Both
  hypotheses are uniquely typed, and spelling the eight-constructor induction
  pattern would be more brittle.
- `Loop.v` contains its local `destruct_match` reflection tactic and two finite
  boolean simplification loops used only to prove smart-constructor equations.

These are local proof-engineering devices, not unbounded proof search and not
semantic assumptions.  Imported CompCert, Flocq, Menhir, and VPL tactics were
not rewritten as part of this project audit.

## File ownership and physical splits

The Extractor and ParallelCodegen splits were compiled as facades and through
direct downstream consumers.  The split improves reader navigation and remote
incremental builds, but it does not make a clean proof build fully parallel:
the correctness layers still form a necessary dependency chain.

Further physical splitting of TilingBandScheduleValidator was prototyped only at
the ownership level and not adopted.  Its large bridges share functor-generated
point types; independent functor instances are not definitionally equal.  A
naive split would add conversion modules and worsen the proofs.  The correct
future split must instantiate the core functor once and pass that exact module
through dependent interfaces.

## Remote CI

The first remote CI restructuring built the proof/binaries once into a CI image
and ran independent test shards from that image.  It also removed duplicate PR
execution of the former full-tiling workflow.  A remote GitHub Actions run
completed in 46 minutes 25 seconds versus 1 hour 37 minutes 46 seconds for the
previous comparable run (about 52.5% lower elapsed time).

The second CI pass is designed for remote behavior, not local timing:

- proof parallelism is derived from available CPUs, cgroup CPU quota, available
  memory, a per-job memory allowance, and an explicit maximum;
- proof defaults allow up to four workers with 3 GiB budget per worker;
- extraction reuses the selected worker count, then the CI script enters
  `Makefile.extr` directly for `polcert` and `polopt`; this avoids re-evaluating
  and repeating the completed Coq/extraction layer;
- test shards are separately bounded and isolated;
- feature branches run once through the PR event; automatic push builds are
  limited to `main` and `extractor`, while manual runs remain available;
- PR, long-lived-branch push, and manual workflows have non-colliding
  concurrency groups;
- branch/PR Docker cache scopes read the main cache but do not overwrite one
  another;
- shard enumeration rejects command failure, empty output, unexpected names,
  duplicates, and missing status files, preventing silent all-zero false passes.
- the second-level source inspection now checks only the live direct checker
  and dispatcher layers; assertions for the removed source-like/structural
  compatibility classifiers and their embedded examples were deleted with
  that dead API rather than left as a stale facade-dependent CI failure.

These settings must be accepted only after a pushed GitHub Actions run.  Local
container timings validate correctness and resource assumptions, not the final
CI performance claim.

## Acceptance gates

The branch is accepted only after all of the following succeed:

1. clean dependency generation and full `coqc` proof build;
2. the repository's admitted-proof scan;
3. extraction and both compiler executables;
4. parallel-current, vector-current, multipar, matmul, legacy, ISS, tiling,
   compatibility, second-level, diamond, and generated-loop suites;
5. pushed GitHub Actions CI, including cache behavior and elapsed-time review.

No optional alternative proof checker is part of this acceptance policy.
