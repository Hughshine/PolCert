# Read-only audit: `polygen/ParallelLoop.v`

> **Resolution on `fix/parallel-interleaving` (2026-08-07).** This inventory and
> the line references below describe commit `9162178`.  The semantic finding is
> fixed: `PTLoopPar` now admits raw `interleave_family` executions and recursively
> models nested parallel bodies.  Safety is represented separately by
> `ordered_par_trace`/`ordered_semantics` and is derived from codegen origin plus
> validator certificates, rather than assumed by target execution semantics.

## Inventory

- 1,319 lines.
- 129 declarations when mutual declarations, constructors, and generated
  `Scheme` declarations are counted separately: 18 definitions, 26 fixpoint
  names, 10 inductive names, 32 constructors, 40 lemma names, and 3 schemes.
- 636 primary proof-body lines; seven proofs have at least 30 lines.
- 40 declarations have confirmed qualified external use; 93 declarations are
  reachable from those public roots.
- Nine top-level names have no repository reference after comments/strings are
  removed.  Several additional private clusters are unreachable from a public
  root; see the CSV rather than treating every member of those clusters as an
  independently dead lemma.
- No `Admitted`, `admit`, `Abort`, `Axiom`, `Conjecture`, `Unshelve`, or
  `dummy_state` occurrence.

Artifacts:

- `/tmp/polcert-parallelloop-declarations.csv`
- `/tmp/polcert-parallelloop-declarations.md`
- `/tmp/polcert-parallelloop-long-proofs.md`
- `/tmp/polcert-parallelloop-external-refs.txt`
- `/tmp/polcert-parallelloop-rg-hits.txt`

## Exact parallel semantic chain

### 1. The semantic constructor assumes safe interleaving

`polygen/ParallelLoop.v:273-277` defines:

```coq
| PTLoopPar : forall d lb ub body env zs trs tr,
    zs = Zrange (...) ->
    Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
    interleave_safe trs tr ->
    par_trace (Loop ParMode (Some d) lb ub body) env tr
```

Therefore a `ParMode` execution exists only after the derivation already
contains `interleave_safe trs tr`.  The loop semantics does not admit an
arbitrary order-preserving scheduler interleaving and later prove it safe.

`interleave_safe` itself is defined at `polygen/ParallelLoop.v:239-248`.  Its
`IS_take` premise requires the chosen point to commute with all unconsumed
points in earlier traces that it crosses.

### 2. The local refinement theorem consumes that assumption

`interleave_safe_refines_concat` at
`polygen/ParallelLoop.v:1002-1076` proves an already-safe interleaving equivalent
to sequential concatenation.  The parallel branch of
`par_trace_refines_erased_stmt` at
`polygen/ParallelLoop.v:1185-1206` gets `Hinter0 : interleave_safe ...` solely by
inverting `PTLoopPar`, then applies that lemma.

The top-level `semantics_refines_erased` theorem at
`polygen/ParallelLoop.v:1297-1317` consequently proves:

> every behavior admitted by the safe-interleaving semantics refines the erased
> sequential loop.

That theorem is correct for the stated semantics.

### 3. A real validator certificate theorem exists

`src/ParallelValidator.v:228-239` defines `parallel_safe_dim` and
`parallel_cert_sound`.  The property says that two flattened polyhedral
instances with the same environment/current-loop prefix but different values
at the certified dimension are `Permutable`.

The executable validator is `check_pprog_parallel_currentb` at
`src/ParallelValidator.v:817-824`; it reduces the doall check to affine
validation between synthetic schedule views.  Its soundness chain is:

- `check_pprog_parallel_currentb_sound`,
  `src/ParallelValidator.v:863-1201`;
- `checked_parallelize_current_sound`,
  `src/ParallelValidator.v:1203-1220`.

Thus the validator theorem itself is substantial and does establish a useful
pairwise commutativity property.

### 4. Parallel codegen correctness does not use certificate soundness

`src/ParallelCodegen.v:403-408` uses only `certified_dim` to replace the tagged
loop mode by `ParMode`.  The public semantic theorem
`annotated_codegen_correct_general` at `src/ParallelCodegen.v:902-922` is
quantified over an arbitrary certificate and assumes
`ParallelLoop.semantics pl st st'`.  It has no `parallel_cert_sound` premise and
does not call `checked_parallelize_current_sound`.

The checked endpoint, `checked_annotated_codegen_correct_general` at
`src/ParallelCodegen.v:1132-1147`, only extracts `trace_safe` (affine expression
convertibility) from the codegen checker.  It still does not derive
`interleave_safe` from the certificate.

At the driver boundary, `driver/ParallelPolOpt.v:29-43` does invoke
`ValidatorCore.checked_parallelize_current` and converts the returned record to
the codegen module's certificate type.  But its correctness proof at
`driver/ParallelPolOpt.v:1128-1144` binds `Hcert` and immediately delegates to
`checked_annotated_codegen_correct_general`; the validator soundness theorem is
never applied.  Repository search finds `checked_parallelize_current_sound`
only in its definition/re-export (`src/Validator.v:87-88`), not in a codegen or
driver correctness proof.

The final compiler theorem (`driver/VerifiedParallelCompilerConfig.v:372-415`)
therefore remains conditional on the same restricted
`ParallelLoop.semantics` premise.

## Gap conclusion

There is a genuine validator-to-parallel-semantics gap if the intended claim is
that a validator certificate makes every actual scheduler interleaving safe.
The present proof establishes only that executions *already carrying an
`interleave_safe` derivation* refine sequential execution.  Operationally the
validator is run, but its proved `parallel_safe_dim` fact is irrelevant to the
codegen correctness theorem.

This is visible from two otherwise unused declarations in
`polygen/ParallelLoop.v`:

- `interleave_family`, lines 222-230, describes unconstrained
  order-preserving interleavings;
- `family_ordered_permutable`, lines 232-237, describes pairwise commutation
  across iteration traces.

Neither is referenced anywhere else in the repository.  They look like the
start of the missing bridge but are not part of any theorem chain.

## Minimum theorem chain needed to close the gap

1. Prove
   `family_ordered_permutable trs -> interleave_family trs tr ->
   interleave_safe trs tr` by induction on `interleave_family`.
2. Define the parallel-loop scheduler semantics with
   `interleave_family trs tr`, not `interleave_safe trs tr`, or provide a
   theorem that every backend behavior yields `interleave_family`.
3. Prove that `parallel_cert_sound pp cert`, together with the codegen-origin
   correspondence for the certified loop dimension, yields
   `family_ordered_permutable trs` for the per-iteration traces generated by
   that loop.
4. Use `checked_parallelize_current_sound` in the driver/codegen correctness
   proof to supply the certificate premise and derive `interleave_safe` for the
   actual chosen interleaving.

Step 3 is the nontrivial part.  `tagged_prepared_codegen_matches` at
`src/ParallelCodegen.v:568-582` proves only structural origin tags and is itself
unused outside its definition.  A trace-level theorem is still needed to tie
generated instruction points to flattened `PolyLang` instances and show that
points from two loop iterations satisfy `same_parallel_slice`.

## Additional semantic limitation

`PTLoopPar` uses `seq_trace` for the body (`ParallelLoop.v:275`), and
`seq_trace` ignores execution modes in its loop constructor
(`ParallelLoop.v:209-213`).  Thus any inner `ParMode` annotation inside an outer
parallel loop is treated sequentially in the formal execution of that outer
loop.  The multi-dimension codegen endpoint may annotate several nested
dimensions (`src/ParallelCodegen.v:431-454`), but the semantics does not model
simultaneous nested parallel scheduling.  This is conservative as an
underapproximation, but it does not justify all behaviors of a backend that
executes nested parallel annotations concurrently.

## Other reachability findings

The most relevant dead items are the intended-bridge definitions above and
`move_front_permutable` (`ParallelLoop.v:804-848`), whose inverse direction is
not used.  Entire conversion/legacy clusters headed by `of_loop`,
`all_origin_none`, and several base-loop bridge lemmas also have no external
use.  They are cleanup candidates, but they are secondary to closing the
certificate/semantics chain.

---

# `polygen/ParallelLoop.v`: proofs with at least 30 body lines

Proof-body counts exclude `Proof.`/`Qed.` and include only the primary name of
a mutual proof block.  There are seven long proofs in this snapshot.

| Line | Declaration | Body lines | Classification | Audit |
|---:|---|---:|---|---|
| 665 | `seq_trace_refines_erased_stmt` (mutual with `..._stmts`) | 77 | Essential semantic bridge | Structural induction over statements/lists.  It turns sequential traces into erased `BaseLoop.loop_semantics`, using affine-expression trace safety.  The loop, sequence, and guard cases are conventional; the mutual proof is long but not automation-heavy.  It is an appropriate dependency of the parallel-loop case because `PTLoopPar` records each iteration with `seq_trace`. |
| 804 | `move_front_permutable` | 35 | Dead proof | No internal or external caller was found.  It proves the inverse movement direction from the one needed by `interleave_safe_refines_concat`; `move_back_permutable` is the live lemma.  Remove only if source compatibility is not required, otherwise mark as a spare symmetric utility. |
| 850 | `move_back_permutable` | 32 | Essential permutation lemma | Moves a selected instruction point behind a prefix by adjacent commutations, preserving semantics modulo `State.eq`.  This is the live engine used by `interleave_safe_refines_concat`.  The induction and non-alias propagation are direct. |
| 940 | `base_loop_semantics_preserve_nonalias_mutual` | 30 | Essential invariant | Mutual structural induction proving `NonAlias` preservation for erased loop semantics.  Needed to continue trace refinement across iterations and statement sequences.  The proof is compact relative to its six constructors. |
| 1002 | `interleave_safe_refines_concat` | 65 | Central parallel semantic lemma | Induction on the *assumed* `interleave_safe` derivation.  In `IS_take`, first refines the remaining output, then moves the selected point behind the unconsumed earlier traces using `move_back_permutable`.  This correctly proves that any already-safe interleaving is equivalent to sequential concatenation.  It does not prove that a validator-certified loop's arbitrary interleaving is `interleave_safe`. |
| 1078 | `par_trace_forall2_refines_erased` | 33 | Essential iteration composition | Lifts per-iteration parallel-trace refinement through `Forall2` and concatenated instruction semantics, transporting the tail across `State.eq`.  Straightforward and correctly propagates `NonAlias`. |
| 1134 | `par_trace_refines_erased_stmt` (mutual with `..._stmts`) | 116 | Central top-level refinement | Seq and vector loops refine their concatenated iteration traces.  The parallel branch obtains `interleave_safe` by inversion of `PTLoopPar`, invokes `interleave_safe_refines_concat`, then uses the sequential trace theorem for each iteration.  This is internally correct, but the crucial safety fact comes from the semantic constructor premise, not a validator certificate. |

No admission markers or `dummy_state` occur.  The file uses 54 `eauto` and 3
`auto` occurrences; the long proofs are governed by structural induction and
inversion, not broad proof search.
