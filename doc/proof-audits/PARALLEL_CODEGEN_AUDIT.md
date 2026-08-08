# ParallelCodegen read-only audit summary

> **Resolution on `fix/parallel-interleaving` (2026-08-07).** This is a
> historical audit of commit `9162178`, not a description of the current proof
> chain.  The checked codegen endpoint now consumes validator certificate
> soundness, maps actual generated traces back to source points through
> `RawCodegenOrigin`, constructs `ordered_semantics`, and only then invokes the
> erasure and prepared-codegen correctness theorems.  The old global-ordering
> theorems remain compatibility APIs and are not used by the checked driver.

## Inventory

- `src/ParallelCodegen.v`: 1,183 lines.
- Audited at repository commit `9162178`; source SHA-256 `785699d75f2aa08259e347de444752b856d097ea9b014f35c294d99c4b8cb5ce`.
- 90 declarations, including nine separately listed mutual members and the generated public projector `cmd_origin_tagged`.
- 53 unique proof bodies; 597 inclusive proof-span lines and 491 nonblank body lines.
- One unique proof body is >=30 lines: `erase_to_loop_stmt_semantics_mutual` (43 lines).
- 11 declarations have direct qualified uses outside the file; their dependency closure reaches 81 of 90 declarations.
- Nine exported declarations are repository-unreachable: the eight-member origin-depth/matching chain and `erase_to_loop_stmts_semantics`.

Generated files:

- `/tmp/parallel-codegen-proof-inventory.csv`: declaration/proof/caller/external-use/reachability inventory.
- `/tmp/parallel-codegen-declaration-audit.csv`: per-declaration responsibility, complexity, issue, priority, risk, and API constraint.
- `/tmp/parallel-codegen-internal-edges.csv`: internal caller-to-callee graph.
- `/tmp/parallel-codegen-qualified-external-uses.csv`: exact qualified uses in other Rocq files.
- `/tmp/parallel-codegen-proof-index.md`: counts, roots, and long-proof index.
- `/tmp/parallel-codegen-long-proofs.md`: complete >=30-line proof audit plus repeated-family analysis.

## What this file actually proves

The file is mostly a composition layer:

1. Convert `PolIRs.Loop` syntax to an annotated `ParallelLoop`, recording structural loop depth, and erase it back.
2. Show expression/test evaluation and erased structured-loop semantics survive the cross-module AST conversion.
3. Add parallel or vector annotations at certificate-selected depths without changing erased loop syntax.
4. Check that instruction argument expressions can be converted to affine form; vector acceptance additionally requires at least one structurally innermost vector annotation.
5. Use `ParallelLoop.semantics_refines_erased`, then existing `PrepareCodegen` correctness, to relate an accepted annotated execution to polyhedral instance-list semantics.
6. Try optimized code generation first and raw code generation second, accepting either only after the executable target check succeeds.

The difficult proof that safe parallel interleavings refine sequential execution is in `polygen/ParallelLoop.v`, not here. The difficult proof that a dimension has the declarative doall property is in `src/ParallelValidator.v`, not here.

## P0 findings

### 1. Validator soundness is disconnected from codegen correctness

`ParallelValidator.checked_parallelize_current_sound` proves `parallel_cert_sound`, i.e. `parallel_safe_dim` for the certified dimension. Repository search finds no consumer of `parallel_cert_sound` except its forwarding alias in `Validator.v`.

In contrast, `ParallelCodegen` correctness accepts a certificate only to read `certified_dim`; none of its theorems assumes or derives `parallel_cert_sound`. Its top-level theorem assumes `ParallelLoop.semantics pl st st'` and, through the checked wrapper, derives only `ParallelLoop.trace_safe pl` (affine instruction arguments).

The theorem is internally valid because `ParallelLoop.PTLoopPar` admits only traces carrying an `interleave_safe` proof. Thus it proves:

> every execution already admitted by the safe-interleaving semantics refines the sequential erased loop.

It does not by itself prove:

> the validator certificate makes every execution of the intended parallel backend satisfy that safe-interleaving premise.

The unused origin-depth chain (`tagged_from_depth_*`, `codegen_matches_current_dims`, and `tagged_prepared_codegen_matches`) looks like the beginning of the missing connection, but it only proves structural depth tagging. A stronger integration theorem would also need to connect generated-loop iteration traces back to polyhedral instances and use `parallel_safe_dim` to discharge the required cross-iteration `Permutable` facts.

This is a semantic contract issue, not a readability refactor. Preserve all existing theorem names/types. Before making paper-level parallel-validation claims, add and review a separately named stronger theorem or explicitly state that the semantics quantifies only over safe interleavings.

### 2. One brittle goal-shape tactic

`erase_to_loop_stmt_semantics_mutual` uses the file's only `lazymatch goal` after an unlabelled inversion to recover the loop iteration premise. Replace it with a named inversion premise and a direct call to the iteration-lifting lemma. Keep the mutual induction and its named motives.

### 3. Most proof volume is duplicated composition

Five wrapper families occupy 342/597 proof-span lines (57%). The six annotated/refinement and six correctness paths are alpha-equivalent across normal/raw and parallel/vector/many variants. Three fallback inversion proofs also repeat the same two-attempt control flow.

Introduce `Local` generic lemmas for:

- monadic codegen result plus erasure-preserving annotation;
- annotated execution plus `ParallelLoop.semantics_refines_erased`;
- prepared-codegen correctness composition;
- checked optimized/raw fallback inversion over a boolean checker and its sound predicate.

Keep every existing public definition/theorem as a short wrapper. This has low proof risk and gives the largest readability gain.

## P1 findings

- Parallel and vector annotation-erasure mutual proofs are line-for-line duplicates. Prefer one generic mode-change erasure bridge, or derive them through existing `ParallelLoop.erase_parallelize_dim_*` / `erase_vectorize_dim_*` facts if the cross-functor conversion makes that clean.
- `all_es_safeb_*` and `vector_codegen_safeb_*` decide properties defined in `ParallelLoop`; their natural ownership is beside `ParallelLoop.trace_safe`. Move implementation/soundness there and retain public forwarding aliases here.
- `iter_semantics_refine_exact` is a generic relation-monotonicity lemma. A more general state-equivalence version already exists in `Extractor.v`, but importing Extractor would invert dependencies. Put the generic fact in a common IterSem utility instead.
- `erase_to_loop_stmts_semantics` is a harmless exported projection with no repository caller. Preserve it unless an explicit API-breaking cleanup is approved.
- The vector checker proves both trace safety and innermost annotation placement, but semantic correctness discards the innermost component because current `VecMode` semantics is sequential-order. Treat innermost as a backend acceptance condition and document that boundary.

## Recommended order

1. P0 semantic contract review: decide and state what parallel/vector execution model the endpoint theorem must cover; add a stronger theorem rather than altering current public contracts.
2. P0 low-risk proof cleanup: remove the single goal-shape tactic and add Local generic combinators for the repeated erasure/refinement/correctness/fallback families.
3. P1 ownership cleanup: relocate target-AST boolean reflection and generic IterSem lifting while retaining compatibility wrappers.
4. P1 dead-route review: either integrate the origin-depth chain into the stronger theorem or clearly mark why it remains exported.

No repository files were modified and no build was run.

---

# ParallelCodegen long-proof audit

## Scope and counting

- Source: `src/ParallelCodegen.v` (1,183 lines).
- Snapshot: repository commit `9162178`, source SHA-256 `785699d75f2aa08259e347de444752b856d097ea9b014f35c294d99c4b8cb5ce`.
- Inventory: 90 declarations, counting each mutual member separately and counting the generated public record projector `cmd_origin_tagged`.
- Proof bodies: 53 unique bodies. Nine mutual members share a body with their group owner and are not double-counted.
- Threshold: inclusive `Proof.` through `Qed.`/`Defined.` span >=30 lines.
- Exactly one unique proof body meets the threshold.

## `erase_to_loop_stmt_semantics_mutual` (lines 309-354)

**Span:** 43 lines inclusive; 41 nonblank proof-body lines.
**Public reachability:** transitively reachable from the externally used `erase_to_loop_semantics` and from every annotated-codegen refinement theorem.
**Callers:** the two public projection lemmas `erase_to_loop_stmt_semantics` and `erase_to_loop_stmts_semantics`.

### What it proves

The theorem simultaneously transports semantics for a `ParallelLoop.stmt` and a `ParallelLoop.stmt_list`. Its premise executes `ParallelLoop.erase_stmt` in `ParallelLoop.BaseLoop`; its conclusion executes the structurally converted `erase_to_loop_stmt` in `PolIRs.Loop`. It does not prove parallel reordering correct. At this point all execution-mode annotations have already been erased.

The six induction cases are:

1. Loop: preserve evaluation of lower and upper bounds, then lift each iteration-body step from the BaseLoop relation to the PolIRs Loop relation.
2. Instruction: preserve evaluation of the instruction argument list.
3. Sequence node: apply the statement-list induction hypothesis.
4. Guard: preserve the test result and transport the taken body.
5. Empty statement list: reconstruct empty-sequence semantics.
6. Nonempty statement list: transport head and tail semantics separately.

### Why it is long

The length comes from the six constructors of the mutual AST and their semantic constructors. The choice of mutual structural induction is appropriate; this is not an incorrectly generalized induction and it does not contain deep arithmetic or dependence reasoning. The loop case requires the generic `iter_semantics_refine_exact` helper because Rocq's iteration relation is parameterized by its per-element transition relation.

### Readability and brittleness

- Lines 318-328 use `lazymatch goal` to find an iteration-semantics hypothesis created by an unlabelled `inversion Hsem`. This is the only goal-shape tactic in the file. It is brittle under constructor or hypothesis-shape changes and hides which premise drives the loop case.
- Eight `eauto` calls occur in the proof. Most merely pass a just-inverted premise, but they make the Guard, Seq, and Instr cases less explicit than necessary.
- `erase_stmt_sem_goal` and `erase_stmts_sem_goal` are good named motives. They make the combined induction substantially easier to read and should remain.

### Existing lemmas and ownership

- `iter_semantics_refine_exact` immediately above is exactly the helper required here.
- `src/Extractor.v:7155` contains the more general `iter_semantics_refine_with_state_eq`, but `ParallelCodegen` cannot sensibly import the monolithic Extractor module just to reuse it. The reusable relation-lifting fact belongs in the common `Instr.IterSem` utility layer; both files can then use it.
- `ParallelLoop.semantics_refines_erased` is a different and much stronger theorem: it handles safe parallel traces. It cannot replace this cross-functor BaseLoop-to-Loop transport proof.

### Recommended rewrite

P0, low risk, with all public names and types unchanged:

1. Give the loop-case inversion an explicit constructor pattern and name its iteration premise.
2. Apply `iter_semantics_refine_exact` directly to that named premise; remove `lazymatch goal`.
3. Replace `eauto` with the corresponding named premise in the instruction and guard cases where the proof remains equally short.
4. Retain the mutual induction and the two public projection lemmas.

Expected result: modest line reduction, but a material improvement in robustness and reader comprehension. Compressing the six cases into automation would reduce readability and is not recommended.

## Important repeated proof families below the threshold

These proofs are individually shorter than 30 lines, but dominate the file's proof volume and should be handled before micro-shortening the long proof:

| Family | Bodies | Inclusive proof lines | Assessment |
|---|---:|---:|---|
| Codegen erasure, including multi-dimension fold | 7 | 90 | Same bind inversion and annotation-erasure argument |
| Annotated execution refines prepared codegen | 6 | 84 | Six alpha-equivalent 14-line bodies |
| Prepared-codegen correctness composition | 6 | 72 | Six alpha-equivalent 12-line bodies |
| Checked fallback inversion | 3 | 72 | Same two-attempt boolean/control-flow proof |
| Checked endpoint dispatch | 3 | 24 | Same optimized/raw case split |

Together these families occupy 342 of 597 inclusive proof-span lines (57%). Local generic lemmas can remove most of this repetition while every current public theorem remains as a short wrapper.

## Parallel/vector responsibility boundary

The parallel/vector-specific semantic reasoning is not in the long proof above:

- `ParallelLoop.semantics_refines_erased` proves that a derivable annotated execution refines the sequential erased loop.
- A `ParMode` trace is derivable only when `ParallelLoop.interleave_safe` already justifies each cross-iteration move.
- `VecMode` has the same trace order as sequential mode in the current semantics.
- This file then erases annotations and composes with `PrepareCodegen` correctness.

Consequently, the repeated parallel and vector correctness wrappers here reflect common composition, not two independent semantic proofs.
