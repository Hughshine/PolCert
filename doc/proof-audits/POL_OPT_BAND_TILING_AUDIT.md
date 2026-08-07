# Read-only audit: `driver/PolOptBandTiling.v`

## Scope and inventory

- Snapshot: branch `proof/readability-cleanup`, 1,237 source lines.
- 64 top-level declarations: 36 `Definition`, 16 `Lemma`, 12 `Theorem`.
- 499 unique nonblank/noncomment proof-body lines.
- 42 declarations have confirmed qualified uses outside this file; all 64 are
  reachable from those public roots.
- Nine proofs have at least 30 body lines; see
  `/tmp/polcert-poloptbandtiling-long-proofs.md`.
- No `Admitted`, `admit`, `Abort`, `Axiom`, `Conjecture`, `Unshelve`, or
  `dummy_state` occurrence.  Automation is modest (39 `eauto`, 8 `auto`); the
  long proofs are dominated by control-flow case analysis rather than expensive
  search.
- Declaration inventory and raw evidence:
  `/tmp/polcert-poloptbandtiling-declarations.csv`,
  `/tmp/polcert-poloptbandtiling-declarations.md`,
  `/tmp/polcert-poloptbandtiling-external-refs.txt`, and
  `/tmp/polcert-poloptbandtiling-rg-hits.txt`.

## Reader route and theorem chain

Read the file in semantic layers rather than source order:

1. Lines 67-136 define the ordinary/identity source-to-mid affine prefix and
   the mid-to-after direct tiling tail.
2. Lines 411-537 prove the corresponding semantic chain: code generation,
   direct band validation, affine validation, then `State.eq_trans`.
3. Lines 242-270 and 539-582 add optional ISS.  Successful ISS is proved back
   to the original program; failed inference/check/well-formedness selects the
   non-ISS route.
4. Lines 138-223 and 891-1056 define/prove diamond tiling.  It has a distinct
   post-tiling affine step after direct band validation.
5. Lines 271-409 and their 9-line correctness lemmas dispatch from a prepared
   polyhedral program, rejecting scalar-only/export failures.
6. Lines 714-1235 lift the polyhedral results through strengthening and the
   verified extractor to the public loop-to-loop theorems.

The public postcondition is uniform: if an optimized loop returns and runs from
`st` to `st'`, the original loop/program runs from `st` to some `st''` and
`State.eq st' st''`.

## What the band driver actually validates

`TilingSched` is ascribed to `TILING_BAND_DIRECT_RUNTIME_API`, so this driver
sees a deliberately narrow interface: `DirectBandAccepted`, `Rejected`, the
acceptance Boolean, the route computation, and one semantic correctness
theorem.  Thus `PolOptBandTiling.v` composes a band certificate; it does not
reimplement or reopen layout-specific band proofs.

The runtime behind that interface tries proved direct layouts in this order:

1. ordinary common-band strip mining, then uniform grouped/interleaved
   second-level layouts;
2. phase-semantic;
3. scalar-aware;
4. phase-separated ordinary;
5. phase-scalar;
6. semantic-band;
7. mixed second-level.

All successful subchecks collapse to `DirectBandAccepted`; unmatched cases
become `Rejected`.  Consequently:

- `VDefault`, `VDefaultBand`, and `VSecondLevel` all select `Opt_band` in
  `VerifiedCompilerConfig.v`.  Second-level selection is inferred from the
  imported schedule/witness and handled inside the direct runtime, not by a
  separate branch in this driver.
- Identity routes change the source-to-mid importer but reuse the same direct
  band tail.
- Diamond routes also reuse the same direct band tail for mid-to-posttile.
- There is no general affine fallback for a rejected tiling certificate.
  Diamond separately validates posttile-to-final with `validate_general`; that
  is a later schedule-only transformation, not a fallback.

The current two-constructor route intentionally hides which direct subchecker
accepted.  This is sufficient for correctness and keeps the driver proof small,
but it cannot by itself provide variant-level runtime provenance.  Adding tagged
accepted constructors would change the extracted/public route API and is not a
readability-only cleanup.

## Ownership and reachability findings

No dead declaration or dead semantic route was found.  `SBandTilingOptBridge.v`
unfolds or relates most definitions, so even implementation-looking definitions
are externally constrained compatibility surface.  Preserve every existing
name and type; expect bridge proofs to need updates if bodies are factored.

Appropriate ownership in this driver:

- orchestration of import, external runner, validators, code generation, and
  fail-closed policy;
- composition theorems linking their semantic guarantees;
- public loop-to-loop aliases and correctness theorems.

Appropriate ownership elsewhere, already respected:

- layout recognition and the permutable-band/reversal proofs in
  `TilingBandDirectRuntime` and its validator dependencies;
- extractor correctness in `Extractor`;
- strengthening correctness in `Strengthen`;
- affine/general validation and code-generation correctness in their modules.

`finish_strengthened_source_correct` is a driver-glue fact.  It is duplicated
nearly verbatim in `PolOptCorrect.v`, but it should not move into `Extractor.v`
because its premises and proof also mention strengthening and `State.eq`.

## Duplication and narrow refactoring candidates

### P0: local, low-risk readability cleanup

- Add private lemmas saying `reject_tiling` and
  `reject_post_tiling_affine` cannot `mayReturn`.  Replace repeated
  `unfold ...; mayReturn_alarm; contradiction` blocks with these names.
- Factor the accepted semantic core of
  `try_verified_diamond_after_phase_mid_band_correct`; keep the outer executable
  case split explicit.
- Add a short comment at the successful identity+ISS export branch explaining
  why export failure alarms after ISS has already been selected.

These changes preserve all definitions, theorem statements, names, and module
paths.  They should reduce proof noise without increasing abstraction.

### P1: private generic helpers, moderate bridge-proof risk

- Parameterize the source-to-mid importer to share the ordinary and identity
  definitions/correctness proofs at lines 96/117 and 454/496.
- Parameterize the diamond runner to share lines 182/203 and 968/1013.
- Introduce one local lifting theorem for the six public prepared wrappers.  It
  should take a route `PolyLang.t -> imp LoopIR.t` and its from-poly correctness
  theorem, perform extractor-success well-formedness, and call
  `finish_strengthened_source_correct`.

Keep all current definitions/theorems as thin wrappers with exactly their
existing types.  Because `SBandTilingOptBridge.v` unfolds several bodies, compile
that bridge immediately after each factoring step.

### P2: cross-driver cleanup, higher coordination cost

- Move the extractor/strengthen/`State.eq` closure shared with
  `PolOptCorrect.v` into a small driver-level glue module.
- Consider a shared prepared-route lifting theorem used by sequential, band,
  and parallel drivers.

Do this only after local P0/P1 prototypes compile.  A very general higher-order
ISS combinator is not recommended: the ordinary, identity, and diamond policies
have meaningful differences, and abstracting all branch behavior would make the
proof harder to audit.

## Naming and design cautions

- `checked_tiling_schedule_sourceb_first_runtime_validate_route` now aliases a
  complete direct dispatcher, not merely the first ordinary/second-level
  subchecker.  Renaming it would be an API break; a comment at the import site is
  safer.
- `try_diamond_phase_pipeline_from_source_pol_band_with_iss` does not itself
  validate ISS.  It names the runner variant used after ISS selection.  Keep the
  name for compatibility, but explain this separation in the proof map.
- `reject_post_tiling_affine` returns the same alarm for both route constructors.
  It is externally mirrored by the bridge; simplifying its match offers little
  readability benefit.

## Bottom line

The proof architecture is correct and modular: the driver relies on the sealed
direct-band theorem, composes it with affine/ISS/code-generation results, and
finally closes the extractor/strengthening boundary.  The main readability
problem is duplicated orchestration proof, not a missing second-level or diamond
correctness argument.  The safest cleanup is named alarm impossibility plus
small accepted-branch helpers; importer/runner/frontend generalization is viable
if every public wrapper remains and `SBandTilingOptBridge.v` is rebuilt after
each change.

---

# `driver/PolOptBandTiling.v`: proofs with at least 30 body lines

The threshold counts nonblank, noncomment proof-body lines and excludes `Proof.`
and `Qed.`.  The source snapshot has nine such proofs.  None contains an
admission marker, `dummy_state`, or an unbounded search tactic.  Most length is
caused by fail-closed case analysis over executable pipeline code.

| Line | Declaration | Body lines | Role | Assessment and narrow cleanup |
|---:|---|---:|---|---|
| 411 | `try_verified_tiling_after_phase_mid_band_correct` | 32 | Core tiling-tail composition | On the only returning branch, converts the general well-formedness check, applies general code-generation correctness, and sends the resulting target semantics backward through `checked_tiling_schedule_sourceb_first_runtime_validate_route_correct`.  Every import/check/rejection branch is discharged by impossibility of `mayReturn` from an alarm.  The proof is semantically direct.  A local `reject_tiling_never_returns` lemma would remove repeated unfolding without hiding the accepted branch. |
| 454 | `try_phase_pipeline_from_source_pol_band_correct` | 30 | Affine-prefix plus tiling-tail | Establishes target-to-mid semantics with the direct tiling theorem, then mid-to-source semantics with `validate_correct`, and composes the two `State.eq` witnesses.  This is an exact structural twin of the identity version below; parameterizing only the importer gives a small private generic theorem while retaining this name and type. |
| 496 | `try_identity_phase_pipeline_from_source_pol_band_correct` | 30 | Identity-import variant of the affine-prefix proof | Differs from line 454 only in `from_openscop_like_source` versus `from_openscop_schedule_only`.  There is no distinct semantic argument after import: the affine validator establishes the needed relation.  Reuse the same private generic theorem as line 454. |
| 539 | `try_checked_iss_phase_pipeline_from_poly_band_correct` | 33 | ISS wrapper around the ordinary phase route | In the accepted ISS branch, obtains well-formedness of the ISS program, proves the phase route relative to it, applies the ISS cut-semantics theorem back to the original program, and composes `State.eq`.  Failed ISS inference/check/well-formedness deliberately falls back to the non-ISS phase route.  The branch policy is visible and the proof is not intrinsically difficult; only the successful ISS back-composition is worth naming privately. |
| 644 | `try_checked_iss_identity_tiling_phase_pipeline_from_poly_band_correct` | 37 | ISS wrapper around identity tiling | Same ISS back-composition, with an additional export of the accepted ISS program to the identity scheduler.  Failure before ISS acceptance falls back to the non-ISS identity route; failure of the post-ISS export alarms and therefore cannot satisfy the theorem premise.  The asymmetry matches the implementation and deserves a one-line comment because it is easy to misread as an omitted fallback. |
| 891 | `try_verified_diamond_after_phase_mid_band_correct` | 64 | Core diamond-tail composition | This is the one genuinely central long proof.  The successful chain is code generation for `pol_after`, `validate_general_correct` from `pol_after` back to `pol_posttile`, then direct band validation from `pol_posttile` back to `pol_mid`, followed by `State.eq_trans`.  All remaining size is nested failure elimination.  Extract a private accepted-tail lemma after the route and both well-formedness checks have succeeded; retain the outer destructs so the executable control flow remains auditable. |
| 968 | `try_diamond_phase_pipeline_from_source_pol_band_correct` | 32 | Affine-prefix plus diamond-tail | Imports/validates source to `pol_mid`, invokes the diamond-tail theorem, and composes `State.eq`.  It is a textual twin of line 1013 except for the Pluto runner.  A private runner-parameterized theorem can serve both public wrappers. |
| 1013 | `try_diamond_phase_pipeline_from_source_pol_band_with_iss_correct` | 32 | Alternate-runner diamond prefix | Despite the name, this theorem itself does not validate ISS; it invokes `run_pluto_diamond_phase_pipeline_with_iss` on an already selected source program.  The proof is otherwise identical to line 968.  Reuse the same private runner theorem and keep the existing declaration for compatibility. |
| 1058 | `try_checked_iss_diamond_phase_pipeline_from_poly_band_correct` | 31 | ISS wrapper around diamond | Accepted ISS semantics are composed back to the original source after the with-ISS diamond route.  Every ISS failure falls back to the non-ISS diamond route.  This is a legitimate separate policy theorem; sharing only a small successful-ISS composition lemma is preferable to a highly abstract wrapper. |

## Semantic chain to preserve

The diamond success proof should continue to expose this order explicitly:

1. `prepared_codegen_correct_general`: generated loop semantics imply
   `instance_list_semantics pol_after`.
2. `validate_general_correct`: final affine rescheduling implies semantics of
   `pol_posttile` and a first `State.eq`.
3. `checked_tiling_schedule_sourceb_first_runtime_validate_route_correct`: the
   accepted direct band certificate implies semantics of `pol_mid` and a second
   `State.eq`.
4. `State.eq_trans`: compose target-to-posttile and posttile-to-mid equality.

This is not a fallback from band validation to the affine validator.  The
general affine validation is a separate post-tiling transformation in the
diamond pipeline.  If direct band validation rejects, the driver alarms.
