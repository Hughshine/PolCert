# Read-only audit: `src/PrepareCodegen.v`

> **Resolution on `fix/parallel-interleaving` (2026-08-07).** The parallel gap
> described in this historical audit is closed by the pointwise schedule
> certificate and the new `RawCodegenOrigin` trace/source correspondence.  The
> existing state-level PrepareCodegen theorems remain the final sequential
> composition step; the family-preserving facts live in the new bridge.

## Scope and method

- Worktree: `proof/readability-cleanup`.
- File size: 2,091 lines.
- Inventory: 79 top-level declarations: 21 definitions, 51 lemmas, and 7
  theorems.
- Proof volume: 1,434 proof-body lines; 14 proofs have at least 30 body lines.
- Reference analysis strips nested comments and strings, records syntactic
  declaration dependencies, scans every repository `.v` file, and treats a
  qualified use through `PrepareCodegen` or one of its module aliases as a
  confirmed external caller.  Bare same-name hits are retained as candidates
  but not counted as confirmed because this repository contains several
  colliding helper names.
- Reachability from the seven confirmed externally used declarations reaches
  75/79 declarations.  This is syntactic reachability, not a proof-term or
  compiled `.vo` dependency analysis.

Artifacts:

- `/tmp/polcert-preparecodegen-declarations.csv`: declaration-level inventory,
  proof lengths, dependencies/callers, external references, and reachability.
- `/tmp/polcert-preparecodegen-declarations.md`: sectioned readable inventory.
- `/tmp/polcert-preparecodegen-long-proofs.md`: manual review of all 14 long
  proofs and the trace-correspondence gap.
- `/tmp/polcert-preparecodegen-external-refs.txt`: confirmed qualified uses and
  rejected bare-name candidates.
- `/tmp/polcert-preparecodegen-rg-hits.txt`: raw repository search evidence.

No repository file was modified, and no build was run for this read-only audit.

## Responsibility map

The file implements four logically distinct layers:

1. **Representation preparation (lines 36-615).** It pads domains, schedules,
   transformations, and accesses to one codegen dimension, adds zero-tail
   constraints, and maps a prepared scan key back to a source instruction
   point with the same instruction semantics.
2. **Execution-list collection and normalization (lines 617-1284, 1637-1898).**
   It defines a statement/index order, collects the exact source points
   executed by prepared PolyLang semantics, proves uniqueness, sorts them into
   `flatten_instrs`, and obtains source `instance_list_semantics`.
3. **Preparation well-formedness (lines 1286-1503).** It proves that padding
   makes the program acceptable to code generation and preserves the selected
   target dimension.
4. **Loop-codegen endpoints (lines 1900-2089).** It connects CodeGen's
   final-state semantics theorem to the preparation theorem, adds cleanup, and
   provides current-view wrappers for general programs.

The source/padded representation layer is internally coherent.  The principal
readability problem is not hard automation: there are only 22 `eauto`, 8
`auto`, 22 `lia`, and 4 `congruence` occurrences.  Length comes mainly from
repeated positional destruction of `wf_pinstr` conjunctions, vector resize
algebra, and large anonymous conjunction results.

## Confirmed external API

| Declaration | Confirmed external uses | Role |
|---|---:|---|
| `prepare_codegen` | 1 | Prepared PolyLang program used by `driver/PolOpt.v`. |
| `prepare_codegen_semantics_correct` | 1 | Direct prepared-PolyLang semantic endpoint in `driver/PolOpt.v`. |
| `prepared_codegen_raw` | 8 | Raw generated loop, all uses in `src/ParallelCodegen.v`. |
| `prepared_codegen` | 29 | Main generated/cleaned loop endpoint used throughout drivers, tiling, syntax, and parallel codegen. |
| `prepared_codegen_correct` | 15 | Main affine source-semantics theorem. |
| `prepared_codegen_raw_correct_general` | 3 | Raw current-view endpoint used by parallel codegen. |
| `prepared_codegen_correct_general` | 8 | General current-view endpoint used by drivers, tiling, and parallel codegen. |

All module fields remain technically public because `PrepareCodegen` has no
sealing signature.  The table distinguishes declarations that are actually
used outside the file; any refactoring must still preserve every existing name
and type unless a repository-wide compatibility decision is made.

## Zero-reference declarations

| Priority | Declaration | Evidence | Recommendation |
|---|---|---|---|
| P1 | `codegen_wf_pprog` (line 85) | No internal or external reference; only the parameterized `_at` form is used. | Keep the name but mark/document it as a convenience wrapper, or remove only after an explicit API decision. It is not part of the live proof chain. |
| P1 | `prepare_codegen_preserve_ctxt_vars` (line 297) | No caller; proof is `reflexivity`. | Compatibility/documentation wrapper only. Safe to leave; it costs nothing and states a useful interface fact. |
| P0 for parallel work | `source_ip_of_index_length` (line 622) | No current caller. | Do **not** delete. It is a ready-made field of the source-point correspondence required by parallel soundness. |
| P0 for parallel work | `source_ip_of_prefix` (line 630) | No current caller. | Do **not** delete. It directly exposes the environment/source-coordinate projection needed by the parallel bridge. |

There is no evidence of a truly dead proof route among the other 75
declarations.  Almost the whole file is reachable from current external
endpoints.

## Ownership and duplication

### Keep in `PrepareCodegen`

- `source_cols`, `codegen_target_dim`, `depth_tail_zero`, readiness predicates.
- `encode_depth_in_domain`, `prepare_pi`, `prepare_codegen`, and `source_ip_of`.
- The forward/reverse prepared-scan and source-instance correspondence lemmas.
- The preparation correctness theorems and public codegen wrappers.

### Move implementation to shared utilities, preserve old aliases

- `firstn_resize`: generic vector/list resize fact.
- `fold_left_max_le_bound`: generic natural-number fold fact.
- `lex_compare_eq_is_eq`: generic lexicographic/vector equality fact.
- `exact_listzzs_cols_app` and
  `exact_listzzs_cols_implies_poly_nrl_le`: generic exact-column facts; identical
  names also exist in `StrengthenDomain.v`, which is evidence of duplicated
  utility ownership rather than two domain-specific concepts.
- A new shared `resize_prefix_tail` lemma should replace the duplicated
  decompositions in `encode_depth_in_domain_in_poly` and
  `source_resize_eq_implies_prepare_eq`.

No declaration should disappear from the current module path during this
cleanup.  The low-risk pattern is: implement the generic theorem in the utility
module, then retain the existing `PrepareCodegen.<name>` as a one-line proof or
alias.

## The existing source-instance bridge

The useful theorem chain is already bidirectional:

1. `prepare_env_scan_true_implies_source_ip_props` (481) maps every accepted
   prepared scan key `(n,p)` to `source_ip_of ...`, proving source membership,
   environment prefix, exact source width, and padded-tail constraints.
2. `prepare_step_semantics_to_source_ip_sema` (545) proves that the prepared
   execution step executes that source point.
3. `prepare_poly_semantics_collect` (1057) inductively collects the exact
   executed source-point list, with semantics, schedule sortedness, `NoDup`, and
   an iff membership characterization.
4. `source_ip_props_imply_prepare_env_scan_true` (1565) and
   `source_ip_of_self` (1637) prove the reverse membership direction required
   for a complete flattened list.
5. `prepare_codegen_semantics_correct` (1718) sorts the collected execution
   list by source statement/index and proves `flatten_instrs`.

This is strong enough for sequential end-to-end correctness.  It is also the
right *second half* of a parallel proof.

## Parallel trace-to-flattened-instance gap

`ParallelValidator.parallel_safe_dim` quantifies over a source
`flatten_instrs` list and proves that two source points in different values of
the selected current coordinate commute.  `ParallelLoop.PTLoopPar`, however,
requires `interleave_safe trs tr`, where `trs` is the family of generated-loop
instruction traces, one trace per loop iteration.  Connecting them requires a
pointwise and family-preserving origin map.

`PrepareCodegen` does not currently provide that first half:

- `CodeGen.complete_generate_many_preserve_sem` (`polygen/CodeGen.v:102-139`)
  converts final `Loop.loop_semantics` into `PolyLang.env_poly_semantics`; its
  conclusion contains neither the Loop instruction list nor its per-iteration
  partition.
- `prepared_codegen_raw_correct` consumes that final-state theorem and then
  hides the collected source list behind `instance_list_semantics`.
- Loop has `loop_instance_list_semantics` and
  `loop_semantics_aux_implies_instance_list` (`polygen/Loop.v:325-393`), but no
  CodeGen/ASTGen/LoopGen theorem relates those generated points to prepared scan
  keys or source points.
- `Loop.mk_instr_point` and `source_ip_of` are not definitionally the same
  representation.  In particular, the former sets `ip_nth := 0`; a bespoke
  semantic/origin relation is necessary.
- `ParallelCodegen.codegen_matches_current_dims` only proves syntactic tags
  were assigned from the top and does not relate tag `d` to source current
  coordinate `d` (`src/ParallelCodegen.v:397-401`).

Therefore none of the current `PrepareCodegen` endpoints can by itself derive
the `interleave_safe` premise.  The current parallel correctness theorems still
take `ParallelLoop.trace_safe` and semantics whose `PTLoopPar` constructor
already contains that premise; they do not derive it from the validator
certificate.

## Minimum strengthening for parallel soundness

The strongest existing pieces to reuse are:

- `prepare_env_scan_true_implies_source_ip_props`;
- `prepare_step_semantics_to_source_ip_sema`;
- `source_ip_of_index_length` and `source_ip_of_prefix`;
- `prepare_poly_semantics_collect`, especially its exact membership iff;
- `source_ip_props_imply_prepare_env_scan_true` and `source_ip_of_self`.

The missing addition is a trace-preserving codegen theorem.  A useful interface
should relate a structured generated loop trace to a shared source
`flatten_instrs` witness and retain, for every loop iteration, the source
current-coordinate origin.  A flat existential instruction list is not enough.
The proof will likely need induction at the ASTGen/LoopGen boundary, because
that is where loop nesting and schedule dimensions are still visible.

Recommended implementation order:

1. Add a named `prepared_execution_witness` record and a stronger sibling of
   `prepare_poly_semantics_collect`; keep the current theorem as a wrapper.
2. Add a point relation between a generated Loop trace point and its
   `source_ip_of` point.  State it in terms of source membership, executable
   instruction/arguments, environment prefix, and current coordinates, not
   record equality.
3. Prove a structured/raw CodeGen correspondence theorem that retains each
   loop iteration's trace family and the coordinate represented by that loop.
4. Use `parallel_safe_dim` to establish `family_ordered_permutable`, then prove
   the general lemma that an allowed interleaving of such a family satisfies
   `interleave_safe`.
5. Integrate first with `tagged_prepared_codegen_raw`.  Only afterward lift
   through cleanup by proving explicit tag/origin remapping for singleton-loop
   elimination and other cleanup rewrites.
6. Preserve all current public correctness theorem statements as corollaries.

## Risks

- **High: cleanup changes loop origin.** Singleton elimination deletes a loop
  and substitutes its value, so syntactic tag depth after cleanup need not equal
  the source current-coordinate number.  Existing semantic equivalence is not
  an origin-preservation theorem.
- **High: trace partition loss.** Once CodeGen correctness is reduced to final
  state semantics, the sibling-iteration family required by `PTLoopPar` cannot
  be reconstructed without a new structural theorem.
- **Medium: point representation mismatch.** Generated Loop points and source
  PolyLang points differ in statement number, timestamp, index orientation,
  and transformation representation.  Requiring equality or existing
  `eq_except_sched` would make the theorem false for ordinary multi-statement
  programs.
- **Medium: dimension convention.** Top-level Loop environments are initialized
  through `rev`, while loop iterations are prepended.  The new relation must
  state and prove the exact reversal/current-coordinate convention rather than
  infer it from list position informally.
- **Low: internal cleanup.** Named witness records, helper projections, and
  generic resize lemmas can be introduced behind compatibility wrappers with
  no public behavior or theorem-type change.



---

# PrepareCodegen.v long-proof audit

Scope: every proof with at least 30 body lines in `src/PrepareCodegen.v`.  Line
numbers refer to the current `proof/readability-cleanup` worktree.  "Intrinsic"
means that the proof is carrying a real semantic invariant; "bookkeeping"
means that most of its length comes from unpacking records or translating
between encodings.

| Declaration | Lines | Body | What the proof establishes | Complexity and recommended treatment | Parallel correspondence value |
|---|---:|---:|---|---|---|
| `encode_depth_in_domain_in_poly` | 227-295 | 59 | A prepared-domain point projects to a source-domain point and has a zero padded tail. | Intrinsic two-part padding invariant, but the two halves repeat resize/split facts. Extract a generic `resize_prefix_tail` lemma and keep this theorem as the forward domain view. | **Directly useful.** Supplies the source-coordinate projection and zero-tail fact for each prepared scan key. |
| `prepare_pi_current_src_args_in_dim_affine` | 437-479 | 34 | Under the affine/identity witness, prepared source arguments equal evaluation of the padded transformation. | Essential representation bridge. Length is mostly unfolding `current_*` definitions and proving a nested resize identity. Factor a lemma for evaluating a resized affine list under a padded point. | **Directly useful.** It is the local instruction-argument preservation fact needed by a point correspondence. |
| `prepare_env_scan_true_implies_source_ip_props` | 481-543 | 44 | A key accepted by the prepared scan determines a well-formed source point: environment prefix, `belongs_to`, source index length, padded self-equality, and zero tail. | Essential, well-scoped theorem, but the five conjuncts should be named by a record rather than destructed positionally. Keep its present name/type as a wrapper. | **Primary reusable theorem.** This is the prepared-key to flattened-source-instance half of the desired bridge. |
| `prepare_step_semantics_to_source_ip_sema` | 545-615 | 58 | One prepared PolyLang execution step is the semantics of its recovered source `InstrPoint`. | Intrinsic semantic bridge. Much of the proof repeatedly destructs `wf_pinstr`; introduce named projections/helper facts for the affine witness and exact transformation width. | **Useful but insufficient alone.** It starts from a prepared `poly_semantics` step, not from a generated Loop/ParallelLoop trace point. |
| `lex_compare_eq_is_eq` | 677-713 | 31 | Equality returned by vector lexicographic comparison implies boolean vector equality, including zero-padding behavior. | Generic list/vector-ordering fact misplaced in `PrepareCodegen`. Move the implementation to `LinalgExt` or the ordering utility and retain an alias here if the name must remain visible. | Indirect only, through uniqueness/sorting. |
| `source_resize_eq_implies_prepare_eq` | 856-912 | 46 | Equal source prefixes plus null padded tails imply equality of the prepared scan keys. | Intrinsic injectivity of the padding representation. The two near-identical `Hsplitp`/`Hsplitq` blocks should use one generic prefix-tail decomposition lemma. | Useful for proving a pointwise map is injective and for excluding duplicate trace origins. |
| `prepare_env_scan_true_source_ip_eq_implies_same_scan_key` | 914-969 | 38 | Equal recovered source points from two accepted scan keys imply the same statement, source instruction, and prepared key. | Essential uniqueness theorem. Its unused `Hwfpi1` local fact is noise; rely on the forward-properties record and the padding injectivity lemma. | Useful if the correspondence needs uniqueness, but not needed merely to transfer pairwise permutability. |
| `prepare_poly_semantics_collect` | 1057-1284 | 201 | Recovers the exact source-instance execution list from prepared PolyLang semantics; proves step semantics, schedule sortedness, no duplicates, and an iff membership characterization. | **Central and intrinsically nontrivial**, but too many invariants are threaded as an anonymous conjunction. Introduce a named witness record and split the induction-step obligations into (1) source step, (2) schedule minimum, (3) fresh key, and (4) exact membership. Keep the current theorem as a tuple-producing compatibility wrapper. | **Strongest existing reusable theorem.** Its exact membership iff is the endpoint of a trace-to-source bridge, but the input has already forgotten generated-loop trace structure. |
| `prepare_codegen_preserves_ready_at` | 1286-1349 | 58 | Padding makes every instruction codegen-ready at the selected target dimension. | Mostly record bookkeeping and duplicated source-column bounds. Add a helper `source_cols_le_target` and named projections for `wf_pinstr`; theorem itself is conceptually simple. | Supplies dimension/width premises but no trace relation. |
| `encode_depth_in_domain_from_source` | 1505-1563 | 50 | Every well-sized source-domain point belongs to the padded prepared domain. | Intrinsic reverse of line 227. Share a single padded-domain equivalence theorem, then derive the current forward and reverse names as wrappers. | **Directly useful for completeness.** It embeds source flattened instances into prepared scan keys. |
| `source_ip_props_imply_prepare_env_scan_true` | 1565-1635 | 57 | A source point with the right environment prefix, membership, and width is accepted by the prepared scan. | Essential reverse mapping. Most length is recovering fixed-width vector equality. Package premises as a source-point record and keep the old theorem signature as a wrapper. | **Primary reusable theorem.** It gives the flattened-source-instance to prepared-key direction. |
| `source_like_points_imply_NoDupA_np` | 1658-1716 | 42 | Ordinary `NoDup` plus source-point membership facts implies `NoDupA np_eq`, which is required by the final sort proof. | Sorting-specific, not core preparation semantics. Move behind a helper module/section for source-order normalization. The proof is otherwise structurally reasonable. | Not needed for parallel family correspondence unless the proof chooses a global canonical sorted list. |
| `prepare_codegen_semantics_correct` | 1718-1898 | 174 | Converts prepared PolyLang semantics into source `instance_list_semantics`: collect execution points, sort them by source statement/index, prove `flatten_instrs`, and reuse the original schedule order for execution. | **Central but combines two independent stages.** Split into a strong witness theorem exposing `exec_ipl` and its exact origin map, then a normalization theorem that sorts the witness into `flatten_instrs`; preserve the present endpoint unchanged. | Useful endpoint, but currently hides exactly the witness and membership relation needed by parallel proofs. Add a stronger sibling theorem rather than weakening/changing this one. |
| `prepared_codegen_raw_correct` | 1907-2027 | 113 | Lifts raw Loop codegen semantics to prepared PolyLang semantics via `complete_generate_many_preserve_sem`, then invokes preparation correctness. | Mostly generator plumbing and repeated readiness reconstruction. A lower theorem should package codegen premises (`cols`, prepared instructions, current env dimension). Keep this theorem as the public wrapper. | **Critical loss point.** `complete_generate_many_preserve_sem` returns only final-state `env_poly_semantics`; it does not relate the generated loop trace, loop nesting, or iteration family to prepared/source points. |

## Detailed observations

### Central witness should be named

The result at lines 1072-1081 is already a useful semantic object, not merely
an existential convenience.  A compatible refactoring can introduce:

```coq
Record prepared_execution_witness
    (pis : list PolyLang.PolyInstr)
    (varctxt : list Instr.ident)
    (to_scan : nat -> list Z -> bool)
    (st1 st2 : State.t) := {
  pew_points : list PolyLang.InstrPoint;
  pew_semantics :
    PolyLang.instr_point_list_semantics pew_points st1 st2;
  pew_schedule_sorted :
    Sorted PolyLang.instr_point_sched_le pew_points;
  pew_nodup : NoDup pew_points;
  pew_origin : forall ip,
    In ip pew_points <->
    exists n p pi,
      nth_error pis n = Some pi /\
      to_scan n p = true /\
      ip = source_ip_of (length varctxt) n pi p
}.
```

The existing `prepare_poly_semantics_collect` can immediately project this
record back to its current nested-conjunction result, so callers and public
names remain unchanged.

### Sorting is not the parallel bridge

Lines 1769-1897 build a canonical source `flatten_instrs` list by sorting the
actual prepared execution list by `(ip_nth, ip_index)`.  This is correct for the
sequential codegen endpoint.  For parallel soundness, sorting a global list is
too weak: `PTLoopPar` requires pairwise commutativity between points belonging
to *different iteration traces* in `trs`.  A proof must retain that family
partition and the loop coordinate that selected each member; neither is
recoverable from final-state semantics or from a single flattened list without
an additional origin theorem.

### Required stronger codegen theorem

The missing theorem belongs below or alongside `CodeGen.complete_generate_many_preserve_sem`,
not in the padding algebra.  Its useful result must retain, for each generated
loop subtree and iteration `z`, a relation between every `Loop.mk_instr_point`
in that iteration's trace and a source `PolyLang.InstrPoint`.  At minimum the
relation must prove:

1. membership in the same source `flatten_instrs` witness;
2. equality of executable instruction and evaluated arguments (enough to
   transfer `Permutable`);
3. the source environment prefix is the initialized context;
4. source current coordinates before certified dimension `d` agree for
   points in sibling iterations;
5. source coordinate `d` is the loop iteration value `z`;
6. distinct sibling iterations imply `different_dim_at d`.

The existing Loop point itself cannot simply be asserted equal to the source
point: `Loop.mk_instr_point` sets `ip_nth := 0` and uses the loop environment as
both index and timestamp (`polygen/Loop.v:308-320`), while `source_ip_of` keeps
the source statement number, source-sized index, source transformation, and
source schedule (`src/PrepareCodegen.v:115-127`).  A named correspondence
relation is therefore required.  `eq_except_sched` is also too strong whenever
the source statement number is nonzero.

### Raw versus cleaned codegen

Prove the structural correspondence for `prepared_codegen_raw` first.  The
cleaned endpoint applies `LoopSingletonCleanup.cleanup`, whose singleton-loop
elimination substitutes the bound into the body and removes the loop node
(`polygen/LoopSingletonCleanup.v:303-318`).  Its current correctness theorem
preserves only `Loop.loop_semantics` (`:320-375`, `:394-411`), not loop-origin
metadata.  Moreover, `ParallelCodegen.tag_loop` numbers loops by the cleaned
syntactic nesting, and `codegen_matches_current_dims` records only
`tagged_from_top`; its `pp` argument is unused (`src/ParallelCodegen.v:387-401`).
Lifting the trace-origin theorem through cleanup therefore needs an explicit
origin-remapping theorem, not just `cleanup_correct`.
