# Parallel certificate-to-codegen soundness audit

> **Resolution on `fix/parallel-interleaving` (2026-08-07).** This document
> records the pre-fix audit at commit `9162178`; its gap conclusion is historical.
> `PTLoopPar` now uses unrestricted `interleave_family` traces, the validator
> certifies a padded schedule coordinate pointwise, and `RawCodegenOrigin` plus
> `ParallelCodegen` connect each actual generated trace to source instances.
> The checked single- and multi-coordinate endpoints consume those certificates
> to construct `ordered_semantics` before applying the erasure refinement.
> Metadata-preserving cleanup is reflected back to the same certified raw
> program, with executable trace-safety gates for every required stage.

## Scope and verdict

- Snapshot: commit `91621785168a74394f2b9c771bdd8427acc618b7`.
- This was a read-only source audit. No build was run and no repository file was changed.
- The existing Rocq theorem is internally sound for the semantics it states.
- The final theorem does **not** prove that the static doall certificate makes every ordinary scheduler/backend interleaving of emitted `parallel for` code source-equivalent.
- This is therefore a specification/integration gap relative to a real-parallel-execution claim, not a false theorem or inconsistency in Rocq.
- Two additional connections are absent: certified current-coordinate dimension to generated structural loop, and nested/multi-parallel annotations to nested parallel execution.

## Exact end-to-end path

### 1. Static validator proves a real doall property

`src/ParallelValidator.v:42-44` defines a certificate containing only `certified_dim : nat`.

`src/ParallelValidator.v:116-141` splits an instruction point into the external environment and current coordinates. `same_parallel_slice d` means:

1. equal external environment;
2. equal current-coordinate prefix before `d`;
3. different coordinate at `d`.

`src/ParallelValidator.v:228-239` defines:

```coq
parallel_safe_dim pp d :=
  forall envv ipl tau1 tau2,
    length envv = length (pprog_varctxt pp) ->
    flatten_instrs envv (pprog_pis pp) ipl ->
    In tau1 ipl -> In tau2 ipl ->
    same_parallel_slice d tau1 tau2 ->
    ILSema.Permutable tau1 tau2.
```

Thus the declarative property really says that any two source/polyhedral instruction instances in distinct iterations of current dimension `d`, under the same outer prefix, commute.

`src/ParallelValidator.v:817-831` implements the checker by reducing the property to affine validation over two synthetic schedule views. `check_pprog_parallel_currentb_sound` at lines 863-866 proves `parallel_safe_dim`, and `checked_parallelize_current_sound` at lines 1203-1220 packages it as `parallel_cert_sound`.

Repository-wide qualified/unqualified search finds no downstream consumer of `parallel_cert_sound` or `checked_parallelize_current_sound`; `src/Validator.v:80,87-88` only re-export them.

### 2. The driver runs the checker but discards its theorem-level fact

`driver/ParallelPolOpt.v:29-43` executes `checked_parallelize_current`. On success it copies only the natural number `certified_dim` into the separately instantiated codegen certificate and invokes `checked_annotated_codegen`.

In `checked_parallel_current_annotated_codegen_correct` (`driver/ParallelPolOpt.v:1128-1144`), the proof obtains the validator execution as hypothesis `Hcert` at line 1139 but never applies `checked_parallelize_current_sound`; it dispatches directly to codegen correctness at line 1141. The vector proof at lines 1146-1162 is identical.

For multi-parallel, `collect_parallel_current_codegen_certs` (`driver/ParallelPolOpt.v:79-95`) filters dimensions by running the checker, but returns only codegen certificates. `checked_parallel_current_many_annotated_codegen_at_correct` (`driver/ParallelPolOptCorrect.v:94-110`) destructs the collected list and immediately invokes codegen correctness; it proves no `Forall` of certificate soundness.

### 3. Codegen uses the certificate only as a structural depth

`src/ParallelCodegen.v:96-112` tags every loop in the already generated `Loop.t` with its current structural nesting depth. `annotated_codegen` (`src/ParallelCodegen.v:403-415`) reads `certified_dim` and calls `ParallelLoop.parallelize_dim` at that depth. `parallelize_dim_stmt` (`polygen/ParallelLoop.v:63-85`) changes every matching `SeqMode (Some d)` node into `ParMode`.

The only purported origin invariant is:

```coq
Record codegen_matches_current_dims (_pp : PolyLang.t) (pl : ParallelLoop.t) := {
  cmd_origin_tagged : tagged_from_top pl
}.
```

at `src/ParallelCodegen.v:397-401`. The program argument `_pp` is unused; the record proves only structural-depth consistency. `tagged_prepared_codegen_matches` at lines 568-582 proves that weak property, and the entire matching chain has no downstream repository consumer.

The executable acceptance check is unrelated to doall safety. `all_es_safeb` (`src/ParallelCodegen.v:462-513`) only establishes `ParallelLoop.trace_safe`, namely that instruction argument expressions convert to affine form. `checked_annotated_codegen` (`src/ParallelCodegen.v:532-541`) checks only that predicate. It neither requires that a `ParMode` was actually emitted nor checks cross-iteration commutation. The vector version additionally checks structural innermost placement (`src/ParallelCodegen.v:515-555`).

All codegen correctness theorems (`src/ParallelCodegen.v:902-1032`) assume `ParallelLoop.semantics`; none assumes certificate soundness. The checked endpoints at lines 1132-1181 derive only trace safety and then reuse those theorems.

### 4. Target semantics already excludes unsafe interleavings

`polygen/ParallelLoop.v:222-230` defines `interleave_family`, the natural arbitrary merge of per-iteration traces preserving each trace's internal order. `family_ordered_permutable` at lines 232-237 states cross-iteration commutativity. Neither definition is used anywhere else in the repository.

Instead, `interleave_safe` (`polygen/ParallelLoop.v:239-248`) requires a `Permutable` proof whenever an instruction from a later iteration moves before remaining instructions of earlier iterations.

`PTLoopPar` (`polygen/ParallelLoop.v:273-277`) admits a parallel trace only with an `interleave_safe trs tr` premise. Therefore an unsafe physical interleaving simply has no derivation in `ParallelLoop.semantics`.

`interleave_safe_refines_concat` (`polygen/ParallelLoop.v:1002-1076`) serializes an already-safe interleaving. The parallel case of `par_trace_refines_erased_stmt` (`polygen/ParallelLoop.v:1185-1206`) obtains `interleave_safe` directly from the semantic derivation and applies that lemma. `semantics_refines_erased` (`polygen/ParallelLoop.v:1297-1317`) exposes the result to codegen.

Consequently, an arbitrary, even fabricated, `parallel_cert` can be passed directly to `checked_annotated_codegen`. Its correctness theorem still holds because the target semantics admits sequential execution and only those reorderings that already carry the missing commutativity evidence. This demonstrates that the theorem does not establish static certificate-to-runtime safety.

### 5. Final compiler theorems preserve the same conditional contract

`VerifiedParallelCompilerConfig.compile_verified_correct` (`driver/VerifiedParallelCompilerConfig.v:372-415`) states:

```coq
mayReturn (compile_verified cfg loop) pl ->
ParallelLoop.semantics pl st st' ->
exists st'', LoopIR.semantics loop st st'' /\ State.eq st' st''.
```

`compile_correct` at lines 417-432 has the same target-semantic premise. The extracted endpoints, `extracted_parallel_compile_verified_correct` (`driver/ExtractedPipelineCorrect.v:144-248`) and `extracted_parallel_compile_correct` (lines 250-263), retain exactly that premise.

There is no verified operational semantics for the textual backend. `syntax/SLoopMain.ml:179-197` merely prints `ParMode` as `parallel for` and `VecMode` as `vector for`.

The exact current guarantee is:

> Every execution derivable in `ParallelLoop.semantics`, where each performed cross-iteration move already carries the required `Permutable` evidence, is equivalent to some sequential source execution.

It is not:

> Acceptance by the static doall checker makes every order-preserving interleaving of the emitted parallel loop equivalent to the source.

## Independent dimension-correspondence gap

The validator dimension and annotation dimension are not definitionally the same quantity:

- `parallel_safe_dim` indexes `current_coords_of` (`src/ParallelValidator.v:116-141`).
- codegen tags the final structured loop by syntactic nesting depth (`src/ParallelCodegen.v:96-112`).
- `current_view_pprog` preserves `pi_schedule` while replacing the point witness/transformation view (`src/PolyLang.v:1279-1295`).
- affine schedule import changes `pi_schedule` but preserves point witness and transformations (`src/PolyLang.v:886-916`). Thus an interchange/skew can make structural codegen depth `d` denote a schedule coordinate different from current coordinate `d`.
- optimized codegen tags only after `PrepareCodegen.prepared_codegen` runs `Cleanup.cleanup` (`src/PrepareCodegen.v:1900-1905`). `LoopSingletonCleanup.singleton_elim_stmt` removes provably singleton loops (`polygen/LoopSingletonCleanup.v:303-318`), which can shift every deeper structural depth.

No theorem connects a node tagged `Some d` to the source/polyhedral instances selected by `same_parallel_slice d`. This can cause either a no-op accepted annotation when no loop with the depth survives, or selection of a different generated loop.

A subsequent read-only reproduction, recorded in
[PARALLEL_COORDINATE_REPRODUCTION.md](PARALLEL_COORDINATE_REPRODUCTION.md),
makes the representation mismatch concrete.  For an accepted raw route with
certificate `d = 0` and seven schedule rows, raw codegen emits thirteen loop
levels: seven schedule coordinates followed by six reconstructed current
coordinates.  The annotation is placed on schedule loop 0, while current
coordinate 0 appears as a sequential singleton loop at depth 7.  The first
schedule row happens to equal current coordinate 0 in that fixture, so this is
not a wrong-result counterexample; it shows that the generic identification of
the two indices is neither definitional nor proved.

There are two coherent designs, and the implementation must choose one explicitly:

1. If `d` means current-coordinate dimension, codegen must locate a generated loop proven to iterate exactly that coordinate and reject schedules for which no such loop exists.
2. If `d` means generated schedule-loop depth (closer to a Pluto loop directive), the validator must formulate the doall slice using the actual schedule prefix/row represented by that loop, not `nth_error current_coords d`.

## Nested/multi-parallel gap

`PTLoopPar` builds each outer iteration trace with `seq_trace body` (`polygen/ParallelLoop.v:273-276`). `seq_trace.STLoop` ignores a nested loop's mode and concatenates its iterations sequentially (`polygen/ParallelLoop.v:209-213`). Therefore, when generated output contains nested `ParMode`s, the outer parallel semantic rule treats all inner annotations sequentially. It does not model a backend that also schedules inner iterations in parallel.

The multi-current route can emit nested annotations, but its final theorem still quantifies over this outermost-only behavior. Static certification of every requested dimension is run operationally, yet none of those certificate facts is used to justify nested interleavings.

## Vector boundary

`PTLoopVec` (`polygen/ParallelLoop.v:268-272`) concatenates vector-loop iterations in source order. Thus current vector correctness is valid for a sequential-order abstraction, and the innermost check is only a structural backend acceptance condition. It does not model arbitrary SIMD lane execution, memory races, or backend-specific vector semantics. The doall checker is operationally run but proof-theoretically unused here as well.

## Minimal repair sequence

### P0: make the present contract explicit without breaking APIs

1. Preserve all existing theorem names and types.
2. Document `ParallelLoop.semantics` as safe-interleaving semantics and state that the current theorem does not cover a runtime/backend scheduler.
3. Add driver lemmas showing that successful single/vector validation yields `ValidatorCore.parallel_cert_sound` for the returned validator certificate; add a `Forall` analogue for collected multi certificates. This consumes the validator theorem but does not yet close the semantic gap.
4. Add an executable/proved check that an annotation was actually placed. Until dimension correspondence is proved, reject rather than silently accept a missing target loop.

### P0: close the real parallel-execution theorem

1. Define unrestricted parallel traces with `interleave_family`, not `interleave_safe`. For nested parallelism, build each iteration with the unrestricted recursive trace relation rather than `seq_trace`.
2. Prove a generic bridge: pairwise cross-family commutativity plus `interleave_family trs out` implies `interleave_safe trs out`.
3. Define and prove a generated-loop origin invariant. Every annotated loop must identify the source/current or schedule slice it represents, and every target trace instruction must map to a member of `PolyLang.flatten_instrs` while preserving `ILSema.Permutable`.
4. Make the invariant cleanup-aware. A conservative first implementation can reject whenever exact origin cannot be retained. A fuller implementation should carry stable schedule/current-coordinate origin identifiers through AST generation, simplification, singleton elimination, and tagging.
5. From certificate soundness plus the origin invariant, prove `family_ordered_permutable` for every annotated loop's iteration traces.
6. Prove that unrestricted annotated semantics refines the existing safe semantics, then reuse `semantics_refines_erased`, `PrepareCodegen` correctness, and the existing end-to-end composition.
7. Add separately named final theorems over unrestricted/backend semantics first; only strengthen paper-facing claims after these theorems exist.

### Design checkpoint before implementation

The first engineering decision is the meaning of dimension `d`. Current-coordinate certification and generated schedule-loop selection are different abstractions under affine scheduling and cleanup. Patching only the unused `parallel_cert_sound` call would make the proof graph look connected while leaving the central correspondence obligation unresolved.

## Claim calibration

Safe today:

> PolCert checks a declarative doall property and emits annotated loop IR; executions admitted by its safe-interleaving IR semantics refine the source.

Not established today:

> The checked certificate proves every execution of emitted `parallel for`/`vector for`, or nested `--multipar` execution, correct under an ordinary backend scheduler.
