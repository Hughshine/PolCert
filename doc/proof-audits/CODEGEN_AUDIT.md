# Read-only audit: `polygen/CodeGen.v`

> **Resolution on `fix/parallel-interleaving` (2026-08-07).** The reproduced
> current-coordinate/structural-depth mismatch is historical.  Parallel
> validation now targets the padded schedule coordinate actually inserted by
> code generation, and the trace-origin theorem proves that correspondence.

## Scope and artifacts

- File size: 315 lines.
- Declarations: 13 total: 5 definitions, 4 lemmas, and 4 theorems.
- Total proof-body volume: 151 lines.
- Long proofs (at least 30 proof-body lines): one,
  `codegen_correct` with 73 lines.
- No admissions, axioms, dummy states, or local declarations occur in this
  file.
- Reference analysis strips nested comments and strings, records syntactic
  declaration dependencies, scans all repository `.v` files, and counts a use
  as confirmed external only when qualified through `CodeGen` or an alias.

Artifacts:

- `/tmp/polcert-codegen-declarations.csv`
- `/tmp/polcert-codegen-declarations.md`
- `/tmp/polcert-codegen-external-refs.txt`
- `/tmp/polcert-codegen-rg-hits.txt`
- `/tmp/polcert-codegen-long-proofs.md`
- `/tmp/polcert-codegen-dimension-reproduction.md`
- `/tmp/polcert-jacobi-raw-parallel.out`
- `/tmp/polcert-jacobi-raw-parallel.err`
- `/tmp/polcert-jacobi-scheduled-dump.out`

No repository file was modified and no proof build was run.

## Declaration inventory summary

| Line | Declaration | Body | Internal callers | Confirmed external use | Classification |
|---:|---|---:|---:|---:|---|
| 48 | `codegen_target_dim` | 0 | 1 | 0 | Supports unused `codegen_correct`; shadowed by a same-purpose definition in `PrepareCodegen`. |
| 52 | `complete_generate` | 0 | 1 | 0 | Single-instruction generator; root of an unused two-declaration route. |
| 56 | `complete_generate_preserve_sem` | 5 | 0 | 0 | Unused single-instruction correctness endpoint. |
| 75 | `complete_generate_lex_many` | 0 | 2 | 0 | Live internal multi-instruction generator. |
| 80 | `complete_generate_lex_many_preserve_sem` | 6 | 1 | 0 | Live internal semantic composition theorem. |
| 97 | `complete_generate_many` | 0 | 2 | 1 | Confirmed external lower endpoint used by `PrepareCodegen`. |
| 102 | `complete_generate_many_preserve_sem` | 25 | 1 | 1 | Confirmed external lower correctness endpoint used by `PrepareCodegen`. |
| 141 | `codegen` | 0 | 2 | 2 | Confirmed external executable endpoint used by `PrepareCodegen`. |
| 147 | `wf_pprog_implies_pis_have_dimension` | 14 | 1 | 0 | Helper only for unused `codegen_correct`. |
| 169 | `wf_pprog_implies_pis_sched_valid_dimension` | 12 | 1 | 0 | Helper only for unused `codegen_correct`. |
| 190 | `wf_pprog_implies_pis_witness_valid_dimension` | 14 | 0 | 0 | Zero-reference helper; not the environment-dimension equality needed by `codegen_correct`. |
| 215 | `codegen_preserve_wf` | 2 | 0 | 0 | Zero-reference theorem; vacuous because `Loop.wf` is still a `True` placeholder. |
| 226 | `codegen_correct` | 73 | 0 | 0 | Intended whole-program public endpoint, but no repository caller. |

Confirmed external roots are `complete_generate_many`,
`complete_generate_many_preserve_sem`, and `codegen`.  Their dependency closure
contains 5/13 declarations.  The remaining declarations are not necessarily
safe to delete because all non-local module fields are technically public, but
they are outside the repository's current live caller graph.

`driver/PolOpt.v` instantiates `Module CodeGen := CodeGen PolIRs` but does not
refer to any of its fields.  `extraction/extraction.v` imports `CodeGen` but the
actual executable reaches it through the higher PolOpt/PrepareCodegen path.

## Existing semantic chain

The live multi-program path is:

```text
complete_generate_many
  -> PolyLang.elim_schedule
  -> complete_generate_lex_many
       -> ASTGen.generate_loop_many
       -> PolyLoopSimplifier.polyloop_simplify
       -> LoopGen.polyloop_to_loop
```

The correctness proof runs this path backward:

```text
Loop.loop_semantics
  -- LoopGen.polyloop_to_loop_correct -->
PolyLoop.poly_loop_semantics of simplified AST
  -- PolyLoopSimplifier.polyloop_simplify_correct -->
PolyLoop.poly_loop_semantics of generated AST
  -- ASTGen.generate_loop_many_preserves_sem -->
PolyLang.env_poly_lex_semantics of schedule-eliminated program
  -- PolyLang.poly_elim_schedule_semantics_env_preserve -->
PolyLang.env_poly_semantics of original program
```

This chain is sufficient for sequential final-state correctness.  Each public
CodeGen theorem states only a final-state semantic implication.

## Exact trace-information boundary

It is more precise to say the current theorem contracts **never introduce** a
trace correspondence than to say an explicit trace is computed and then
discarded:

1. `complete_generate_lex_many_preserve_sem` starts from
   `Loop.loop_semantics`, not `Loop.loop_instance_list_semantics` or a
   `ParallelLoop.seq_trace` (`CodeGen.v:80-95`).
2. `LoopGen.polyloop_to_loop_correct` is the first lower boundary.  It converts
   that state-only Loop derivation into state-only `PolyLoop.poly_loop_semantics`
   (`LoopGen.v:414-445`).  Its instruction case proves evaluated argument
   equality, but exposes no instruction-point origin.
3. `PolyLoopSimplifier.polyloop_simplify_correct` likewise preserves only
   state-to-state semantics (`PolyLoopSimpl.v:58-64`).
4. `ASTGen.generate_loop_many_preserves_sem` reconstructs a
   `PolyLang.poly_lex_semantics` derivation.  That derivation internally records
   each selected `(statement n, point p)` in `PolyLexProgress`, and the ASTGen
   induction knows each loop iteration `x`; however, the theorem does not pair
   those progress steps with generated Loop instruction points or retain the
   per-iteration trace family.
5. `complete_generate_many_preserve_sem` then removes schedule coordinates and
   returns only `env_poly_semantics` (`CodeGen.v:102-139`).

Thus the earliest theorem requiring a new trace-refined sibling is
`LoopGen.polyloop_to_loop_correct`; the CodeGen wrapper alone cannot recover a
pointwise relation that lower layers never state.  The loss is a theorem/API
gap, not a tactic or readability defect.

## Reusable existing lemmas

### Loop layer

- `Loop.loop_semantics_aux_implies_instance_list` and
  `Loop.loop_semantics_aux_equiv_instance` construct an instruction list while
  preserving the loop/iteration concatenation structure.  A bridge from the
  currently used `Loop.loop_semantics` to the auxiliary/list semantics is still
  absent.
- `Loop.loop_instance_list_semantics_implies_instr_point` provides executable
  point-list semantics when generated expressions are affine.  It does not
  identify source PolyLang points.

### LoopGen and simplification

- The structural induction of `LoopGen.polyloop_to_loop_correct` is reusable.
  In particular, its instruction case uses `make_affine_expr_correct` to prove
  equality of generated and PolyLoop instruction arguments; this is exactly
  the semantic field needed by a point-origin relation.
- `PolyLoopSimplifier.polyloop_simplify_correct` is structurally aligned with
  the AST and does not reorder instructions.  A trace-preservation sibling can
  follow the same induction, but must state how changed guards/bounds preserve
  the same point origins.

### ASTGen

- `ASTGen.generate_loop_many_preserves_sem` already performs the difficult
  induction over generated dimensions.  Lines 682-732 associate each generated
  iteration `x :: env` with the corresponding `env_scan` slice.  This is the
  best proof skeleton for retaining per-iteration families.
- `env_scan_begin`, `env_scan_inj_rev`, `env_scan_extend_many`,
  `poly_lex_semantics_make_npis_subscan`, and `env_scan_make_npis_in` provide
  the prefix, uniqueness, partition, and membership facts needed by a trace
  origin theorem.

### Schedule elimination

- `PolyLang.split3_eq` states the decomposition into environment, inserted
  schedule coordinates, and original coordinates.
- `current_env_dim_in_dim_pi_elim_schedule` and
  `current_src_args_in_dim_pi_elim_schedule_resize` preserve environment size
  and instruction arguments under schedule insertion.
- `poly_elim_schedule_semantics_preserve` lines 7448-7490 explicitly maps a
  schedule-eliminated point to
  `resize es p ++ skipn (k+es) p`.  Its proof is the correct basis for exposing
  a point-origin relation instead of only final semantics.

### PrepareCodegen

- `prepare_env_scan_true_implies_source_ip_props`,
  `prepare_step_semantics_to_source_ip_sema`, and
  `prepare_poly_semantics_collect` can consume the resulting prepared point and
  map it to the source flattened instance.  These are the second half of the
  bridge, as recorded in the PrepareCodegen audit.

## New theorem gap versus readability cleanup

### Readability-only work

- Give `codegen_correct` stable semantic names and package its dimension
  obligations.
- Consolidate the duplicate `codegen_target_dim` ownership with
  `PrepareCodegen`, preserving both old names as compatibility aliases.
- Document the single-instruction `complete_generate` route as legacy or retain
  it behind a small subsection.
- Mark `codegen_preserve_wf` as vacuous until `Loop.wf` is meaningful.
- Retain current declaration names/types even for zero-reference helpers unless
  an explicit external API change is approved.

These changes do not strengthen any correctness claim.

### Required new theorem work

A parallel proof needs a new structured relation, not a refactor of
`complete_generate_many_preserve_sem`.  It must retain:

1. the generated instruction point for every source/prepared progress step;
2. executable instruction/argument equality;
3. the family of points produced by each iteration of each generated loop;
4. the exact coordinate represented by that generated loop;
5. the schedule-elimination map from generated coordinates back to current
   coordinates; and
6. the effect of simplification/cleanup on loop-origin tags.

A flat `Forall2` over complete traces is insufficient because
`ParallelLoop.PTLoopPar` needs the sibling-iteration partition `trs`.  A
structured trace relation indexed by generated AST/Loop nodes is preferable.

The compatible rollout is to add sibling theorems at LoopGen,
PolyLoopSimplifier, ASTGen, and CodeGen, then leave all current state-only
theorems as corollaries or unchanged wrappers.

## Coordinate mismatch found during the audit

The dynamic evidence in `/tmp/polcert-codegen-dimension-reproduction.md`
confirms that raw syntactic tag `d` denotes schedule-elimination coordinate
`d`, while the validator certificate is defined over current coordinate `d`.
In the reproduced accepted raw route, `d=0`, `k=7`, the parallel annotation is
on generated loop `i0`, and current coordinate 0 is reconstructed by the
sequential singleton loop `i7 = i0`.

This fixture happens to have schedule row 0 equal to current coordinate 0, so
it does not demonstrate a bad result.  It demonstrates that the generic
coordinate relation assumed by the annotation code is unstated and not
definitionally true.  An arbitrary affine schedule can mix or permute current
coordinates.

The repair should not blindly use tag `k+d`: that selects the singleton current
reconstruction loop.  To produce useful parallel code, the validator must
certify the generated schedule-loop coordinate/prefix, or codegen must return a
proved mapping from the requested current dimension to an appropriate
generated schedule loop.  Cleanup requires a further origin-remapping theorem.

## Risk ranking

- **P0 correctness gap:** validator current-coordinate certificate is copied
  directly into a generated syntactic loop tag without a schedule/current
  origin theorem.
- **P0 proof gap:** no theorem derives the `PTLoopPar` iteration-family safety
  premise from codegen traces and the certificate.
- **P1 structural work:** trace refinement must cross LoopGen,
  PolyLoopSimplifier, ASTGen, schedule elimination, and cleanup; a CodeGen-only
  wrapper theorem is insufficient.
- **P2 readability:** the only long proof is bookkeeping-heavy but not
  intrinsically difficult; it can be shortened independently.
- **P2 dead/legacy surface:** the single-instruction route, vacuous `Loop.wf`
  theorem, witness-dimension helper, and unused `codegen_correct` endpoint are
  outside the live repository caller graph but should retain compatibility
  names unless deliberately deprecated.



---

# `polygen/CodeGen.v` long-proof audit

Threshold: at least 30 proof-body lines.  The file has exactly one such proof.
Line numbers refer to the current `proof/readability-cleanup` worktree.

## `codegen_correct` (lines 226-313; 73 proof-body lines)

### Statement and role

The theorem is the whole-program wrapper for the original CodeGen path.  From
a successful `codegen pol`, source well-formedness, two dimension/witness
premises, and final `Loop.semantics`, it derives final `PolyLang.semantics`.
There are no qualified callers in the repository.  `PrepareCodegen` uses
`CodeGen.codegen`, but reconstructs the lower-level argument itself through
`complete_generate_many_preserve_sem`; it does not invoke `codegen_correct`.

### Proof structure

1. Lines 240-249 destruct the impure codegen result and whole-program Loop
   semantics, then derive the generated environment length.
2. Lines 250-263 derive `length ctxt <= codegen_target_dim` from source
   well-formedness and the target `Nat.max`.
3. Lines 264-305 invoke `complete_generate_many_preserve_sem` and discharge
   its three program-wide obligations:
   - domains fit the chosen dimension;
   - every point witness has the expected current environment dimension;
   - schedules fit the chosen dimension.
4. Lines 307-312 rebuild `PolyLang.PSemaIntro` around the resulting
   `env_poly_semantics` derivation.

### Readability findings

- The opening `intros. intros loop ...` and subsequent inversions introduce
  unstable names such as `H`, `H0`, `H1`, `H2`, `H3`, `loop0`, `ctxt`, and
  `vars`.  This makes the proof substantially harder to audit than its
  mathematical content warrants.
- The three obligations assembled at lines 277-304 are the actual interface
  between whole-program codegen and `complete_generate_many`.  They should be
  packaged as a named record or one preparation lemma rather than rebuilt
  inside a 73-line proof.
- `Htarget` and `Henvdim` are important nontrivial caller obligations, but the
  proof gives no name to the combined invariant they express.
- `wf_pprog_implies_pis_have_dimension` and
  `wf_pprog_implies_pis_sched_valid_dimension` differ only in which field of
  `wf_pinstr` they project.  Named `wf_pinstr` projections would shorten both
  helpers and the main proof.
- No broad or expensive automation obscures the argument: the entire file has
  six `eauto`, four `auto`, and six `lia` occurrences.  The problem is naming
  and conjunction/inversion bookkeeping, not tactic search.

### Safe cleanup

Keep the current theorem name and type.  Internally:

1. introduce a `codegen_program_obligations` record or helper theorem that
   collects context bound, `pis_have_dimension`, witness environment dimension,
   and schedule row bound;
2. name the fields of the inverted Loop semantics explicitly;
3. call a small `complete_generate_many_program_semantics` wrapper;
4. make `codegen_correct` a short construction of `PSemaIntro`.

This is a readability refactor only.  It does not address the trace theorem
gap below.

### Why this proof cannot establish parallel trace correspondence

The premise contains only `Loop.semantics`, whose inner relation is
state-to-state `Loop.loop_semantics`.  The proof invokes
`complete_generate_many_preserve_sem`, whose conclusion is also state-to-state
`PolyLang.env_poly_semantics`.  At no point is a generated instruction list,
per-loop iteration family, or point-origin relation introduced.  Renaming or
factoring this proof cannot manufacture those missing invariants; a new theorem
contract and supporting lower-layer theorems are required.
