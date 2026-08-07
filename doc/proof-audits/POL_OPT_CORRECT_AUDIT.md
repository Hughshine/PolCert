# `driver/PolOptCorrect.v` declaration audit

## Scope and artifacts

The audit strips comments and strings, records every lemma/theorem, measures
proof spans, computes declaration dependencies and callers, follows module
aliases for qualified external references, and computes reachability from
repository-confirmed external roots.

- `/tmp/polcert-poloptcorrect-declarations.csv`: declaration dependency/caller data
- `/tmp/polcert-poloptcorrect-declarations.md`: sectioned declaration table
- `/tmp/polcert-poloptcorrect-long-proofs.md`: all proofs with at least 30 body lines
- `/tmp/polcert-poloptcorrect-external-refs.txt`: qualified external and bare-name evidence
- `/tmp/polcert-poloptcorrect-rg-hits.txt`: raw repository searches

## Inventory

- 12 declarations: 5 lemmas and 7 theorems.
- 159 proof-body lines.
- Two confirmed repository-external theorem roots:
  `Identity_opt_prepared_correct` and `Affine_opt_prepared_correct`, each used
  by `VerifiedCompilerConfig.v` and `ExtractedPipelineCorrect.v`.
- Four declarations are reachable from those confirmed roots:
  the two roots, `identity_opt_prepared_from_poly_correct`, and the local
  `finish_strengthened_source_correct`.
- Eight declarations, accounting for 107 proof-body lines, are outside that
  confirmed root closure.
- Three exported declarations have no repository caller:
  `Identity_tiling_generic_opt_prepared_correct`, `Opt_correct`, and
  `Opt_with_iss_correct`.
- Only `try_checked_iss_phase_pipeline_from_poly_correct` exceeds 30 proof-body
  lines, at 37 lines.

The reachability result describes this repository's current configurations; it
does not imply that the top-level `Opt*` theorems are conceptually dead.  They
are plausible compatibility/public entry points and should retain their names
and types unless API removal is deliberate.

## Reader-visible theorem chain

The file has two semantic levels.

### Post-extraction correctness

The `*_from_poly_correct` lemmas assume an affine-well-formed polyhedral
program and show that the selected prepared route refines that program.

- Identity code generation is a direct `PrepareCodegen` application.
- The baseline phase route selects the verified phase pipeline, affine
  fallback, or direct code generation according to the executable dispatcher.
- The ISS-aware route first attempts a checked ISS partition; on success it
  composes ISS correctness with the phase pipeline, and on failure it uses the
  baseline route.

### Loop-to-loop correctness

Each prepared theorem performs the same frontend closure:

1. Run `Extractor.extractor` and recover `pol0` from `res_to_alarm`.
2. Strengthen `pol0` into the affine program `pol`.
3. Derive affine well-formedness from extractor success and strengthening.
4. Apply the selected post-extraction correctness theorem.
5. Remove domain strengthening.
6. Apply `Extractor.extractor_correct` to reconstruct a source-loop execution.
7. Compose the route and extractor `State.eq` facts.

`Opt_correct` and `Opt_with_iss_correct` are one-line aliases of the
corresponding prepared theorems.

## Extractor/strengthen/State.eq duplication

`finish_strengthened_source_correct` already gives a useful local boundary for
steps 5--7.  It is called by five prepared theorems.  Its `State.eq_trans`
orientation is explicit and correct:

```text
generated result  ~=  strengthened-program result
strengthened result ~= source-loop result
---------------------------------------------
generated result  ~=  source-loop result
```

However, steps 1--4 surrounding that helper remain copied five times:

- `Opt_prepared_correct`: 16 proof lines
- `Identity_opt_prepared_correct`: 16 proof lines
- `Identity_tiling_generic_opt_prepared_correct`: 17 proof lines
- `Affine_opt_prepared_correct`: 16 proof lines
- `Opt_prepared_with_iss_correct`: 16 proof lines

Together these near-isomorphic wrappers account for 81 of the file's 159 proof
lines.  They differ only in the unfolded executable alias and the selected
post-extraction correctness theorem.

The local `finish_strengthened_source_correct` itself is duplicated almost
verbatim at `driver/PolOptBandTiling.v:714--736`, where six more prepared routes
repeat the surrounding extractor/strengthen/well-formedness template.
`ParallelPolOptCorrect.v` contains the same semantic closure in two forms:

- the `finish_extracted_result` Ltac at lines 1518--1560;
- the theorem `opt_vector_current_result_from_prepared_correct` at
  lines 2302--2342.

The latter is the better model: this recurring proof should be represented by
a theorem, not by a large tactic that synthesizes witnesses and equality
composition invisibly.

## Recommended lifting theorem

Introduce a private sequential theorem parameterized by the prepared
polyhedral route:

```coq
Local Lemma lift_extracted_strengthened_route_correct :
  forall (route : PolyLang.t -> imp LoopIR.t) loop st st' loop',
    (forall pol st st' loop',
       PolyLang.wf_pprog_affine pol ->
       mayReturn (route pol) loop' ->
       LoopIR.semantics loop' st st' ->
       exists st'',
         PolyLang.instance_list_semantics pol st st'' /\
         State.eq st' st'') ->
    mayReturn
      (BIND pol0 <-
         res_to_alarm PolyLang.dummy (Core.Extractor.extractor loop) -;
       route (Core.Strengthen.strengthen_pprog pol0))
      loop' ->
    LoopIR.semantics loop' st st' ->
    exists st_src,
      LoopIR.semantics loop st st_src /\ State.eq st' st_src.
```

Its proof should perform extraction, well-formedness, route correctness,
unstrengthening, extractor correctness, and the final `State.eq_trans`
explicitly.  Each public prepared theorem then unfolds only its alias and
applies this theorem with the route-specific correctness lemma.

This subsumes `finish_strengthened_source_correct` locally and turns each
16-line wrapper into roughly three proof lines.  It also provides a theorem
shape that `PolOptBandTiling` can reuse or reproduce before introducing a
shared driver utility.

## Ownership findings

### Keep in `PolOptCorrect`

- High-level dispatcher correctness for phase and ISS-aware routes.
- Public sequential loop-to-loop theorem names.
- The explicit composition of route correctness with the frontend boundary.

### Shared frontend correctness

The extraction/strengthening lift is not specific to affine, tiling, ISS, band,
parallel, or vector routes.  Its mathematical owners are the extractor and
strengthening correctness interfaces.  After a local prototype compiles in
both sequential files, move the generic theorem to a small driver correctness
utility parameterized by `POLIRS` and a post-extraction route theorem.

Do not move it into `Extractor.v`: the theorem also depends on strengthening,
the prepared route's target semantics, and `State.eq` composition.  A driver
glue module is the appropriate boundary.

### Route-specific proof split

The current organization is inconsistent but workable:

- `Core.affine_opt_prepared_from_poly_correct`,
  `Core.try_phase_pipeline_from_source_pol_correct`, and generic tiling route
  correctness live in `PolOpt.v`.
- Identity, dispatcher, and ISS-aware composition lemmas live here.

For the immediate readability cleanup, retain this split and make the calls
explicit.  Moving all correctness out of `PolOpt.v` would alter the
`POL_OPT_CORE` module interface and create a much larger dependency change.
Document the ownership boundary instead of performing that reorganization as
part of proof cleanup.

## Repetition that should remain visible

The three direct-codegen/fallback branches close with a source semantic witness
and `State.eq_refl`.  These occurrences are route semantics, not accidental
frontend boilerplate.  Similarly, the four ISS failure branches should visibly
fall back to the baseline verified pipeline.  Avoid consolidating them through
opaque Ltac.

## Dead and compatibility routes

- `Identity_tiling_generic_opt_prepared_correct` has no repository caller.  It
  appears to be the older generic tiling entry point, while current configured
  tiling routes are supplied by the band/direct validators.  Retain it as a
  compatibility theorem unless that API is intentionally retired.
- `Opt_correct` and `Opt_with_iss_correct` have no repository caller but are the
  natural top-level named theorems.  Their one-line bodies are appropriate and
  should remain.
- The ISS-aware path is not reachable from the two currently confirmed config
  roots, but it is internally coherent and feeds `Opt_with_iss_correct`; this is
  dormant configuration support, not a dead proof route.

## Remediation order with public interface unchanged

### P0: theorem-level frontend lift

1. Add the private `lift_extracted_strengthened_route_correct` theorem.
2. Convert the five prepared wrappers to applications of it.
3. Keep every public theorem name and type unchanged.

Expected effect: remove roughly 50--60 repetitive proof lines and make the
extractor/strengthen/`State.eq` boundary readable once.

### P1: share with band routes

1. Apply the same theorem pattern in `PolOptBandTiling.v`.
2. Once both instances compile, move the theorem to a small shared driver glue
   module rather than duplicating the local `finish_*` lemma.
3. Prefer the theorem over the large `finish_extracted_result` Ltac used by
   parallel routes; migrate that tactic only in a separate, scoped cleanup.

Risk: low for the local sequential prototype, medium for a cross-file generic
module because functor paths and `mayReturn` result shapes differ among
sequential and parallel routes.

### P2: successful ISS branch readability

Factor the positive ISS composition into a private helper if it improves the
source after P0.  Preserve explicit fallback branches.  Do not remove dormant
public theorem names as part of this change.

## Reader route after cleanup

1. `identity_opt_prepared_from_poly_correct`
2. `try_checked_iss_phase_pipeline_from_poly_correct`
3. `phase_opt_prepared_from_poly_correct`
4. `phase_opt_prepared_from_poly_with_iss_correct`
5. `lift_extracted_strengthened_route_correct`
6. One representative public wrapper, such as `Opt_prepared_correct`
7. `Opt_correct` and `Opt_with_iss_correct`

This route separates transformation correctness from the single frontend
closure and makes the end-to-end equality chain explicit exactly once.

---

# `driver/PolOptCorrect.v` long-proof audit

Threshold: at least 30 proof-body lines.  Counts exclude `Proof.` and the
closing command.  Only one proof crosses the threshold.

| Line | Declaration | Body lines | Ownership | Assessment | Recommended internal refactor |
|---:|---|---:|---|---|---|
| 50 | `try_checked_iss_phase_pipeline_from_poly_correct` | 37 | ISS-aware sequential pipeline composition | The proof mirrors the executable fallback tree.  In the successful ISS branch it proves the inferred program well formed, runs the verified phase pipeline from that program, applies complete-cut ISS validation backward to the source program, and composes the two `State.eq` facts.  Every inference/check/well-formedness failure executes the baseline phase pipeline and reuses its correctness theorem.  The semantic argument is sound and the branching is substantially dictated by the implementation. | Keep the fallback cases visible.  Factor only the successful validated-ISS branch into a private lemma with explicit inputs `(Hiss_check, Hiss_wf, Hopt, Hloop)`; optionally name the baseline fallback theorem application.  Do not replace the branch structure by dense `all: eauto`, because the reader should see that every failed optional ISS step returns to the verified non-ISS route. |

## Mathematical chain in the successful branch

1. `infer_iss_from_source_scop` produces `pol_iss` and witness `w`.
2. `checked_iss_complete_cut_shape_validate` establishes the checked ISS
   relation from `pol` to `pol_iss`.
3. The executable well-formedness check for `pol_iss` is converted to
   `wf_pprog_affine pol_iss`.
4. `try_phase_pipeline_from_source_pol_correct` proves that the generated loop
   refines the ISS-transformed polyhedral program, yielding
   `State.eq st' st_iss`.
5. `checked_iss_complete_cut_shape_validate_semantics_correct` reconstructs a
   source execution, yielding `State.eq st_iss st_src`.
6. `State.eq_trans` produces `State.eq st' st_src`.

The composition direction is correct.  No symmetry is being used implicitly.

## Fallback structure

The four fallback exits are:

- ISS inference returns `Err`;
- ISS inference returns `Okk None`;
- the complete-cut checker returns `false`;
- the inferred ISS program fails the affine well-formedness check.

All four call `Core.try_phase_pipeline_from_source_pol_correct` on the original
program.  This repetition is small and documents fail-closed behavior.  A
private name for the fallback application may improve messages, but a generic
tactic would make the operational proof harder to audit.

## Automation and proof hygiene

- No `Admitted`, `admit`, `Abort`, `Unshelve`, `Axiom`, `Conjecture`, or
  `dummy_state` token occurs in the file.
- The entire file uses 16 `eauto` and 4 `auto` occurrences, with no arithmetic
  automation.  The long proof uses `eauto` mainly for the identical fallback
  calls and the final `State.eq_trans` premises.
- There is no tactic-performance concern visible here.  The dominant cleanup
  opportunity is repeated frontend lifting across several short theorems.
