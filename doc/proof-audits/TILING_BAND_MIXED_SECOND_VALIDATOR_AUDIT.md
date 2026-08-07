# Read-only audit summary: `TilingBandMixedSecondValidator.v`

## Scope and method

- Worktree: `work/proof-readability`, branch `proof/readability-cleanup`.
- Source audited: 3,130 lines, 51 non-`Local` declarations, 33 proofs.
- Call graph: lexical declaration dependencies within the functor plus qualified
  uses from all other repository `.v` files.  The six actual external roots are
  all in `TilingBandDirectRuntime.v`.
- Live closure: 48 declarations (six roots plus 42 dependencies).  Three
  declarations lie outside it.  Since every declaration is exported from the
  functor, "not live" means only that this repository has no current caller;
  it does not prove that external users do not depend on the module path.
- Generated artifacts:
  - `/tmp/tiling_band_mixed_second_declarations.csv`: all 51 declarations with
    spans, proof lengths, dependencies, internal callers, qualified external
    uses, root/closure status, tactic counts, ownership, and recommended action.
  - `/tmp/tiling_band_mixed_second_long_proofs.md`: manual review of all eight
    proofs of at least 30 proof lines, with precise extraction/comment points.

## Reader path and theorem chain

### Mixed grouped second-level route

1. `schedule_head_constant` / `pinstr_head_constant` expose a constant scalar
   phase at the head of a source schedule.
2. `infer_unique_phase_constants` and
   `check_unique_phase_constantsb` infer those phases, require every band to
   start after the scalar phase (`ptb_start = 1`), and check uniqueness.
3. `infer_pprog_mixed_second_level_shape` combines second-level band/recipe
   inference, the grouped second-level target schedule shape, and unique phases.
4. `check_pprog_mixed_second_level_direct` checks the source/witness boundary,
   the shape above, and then calls
   `Core.check_pinstr_list_pluto_componentwise_permutable_bands_direct`.
5. Its correctness theorem turns that Boolean band check into
   `pprog_pluto_componentwise_permutable_bands` and supplies
   `mixed_second_level_local_reversal_bridge_wf_with_env_len` as the local
   semantic bridge.
6. The bridge first proves a reversed pair has the same statement using phase
   uniqueness, then proves a decreasing component in that statement's band.
   The common tiling theorem turns this into source/target semantic equivalence.

This path does not call a general affine validator and has no affine fallback.
The componentwise permutable-band checker is the principal acceptance check.
The grouped schedule-shape check is a representation premise needed to relate
the target timestamp to root tiles, child tiles, and the preserved band; it is
not an alternative correctness validator.

### Phase-separated ordinary route

1. `infer_phase_class_entries` records, for each statement, its scalar phase,
   ordinary band, and tile sizes.
2. `check_phase_class_consistencyb` permits multiple statements in the same
   phase class but requires that equal-phase entries share their band and tile
   sizes.
3. `check_pprog_phase_separated_ordinary_direct` checks source/witness shape,
   ordinary strip mining, uniform schedule arity, phase-class consistency, and
   the same direct componentwise permutable-band checker.
4. `phase_separated_ordinary_reversal_same_class` uses reversal to show equal
   phases and hence equal pair-local band/recipe metadata.
5. `phase_class_ordinary_local_reversal_bridge_wf_with_env_len` passes those two
   facts to `Core.ordinary_pair_local_reversal_bridge_wf_with_env_len`.

This is the clearer architecture and should be the model for second-level:
Mixed proves pair-local compatibility; Core owns the band algorithm.

## Main structural finding

`mixed_second_level_local_reversal_bridge_wf_with_env_len` is 586 proof lines,
but almost all of it is a second copy of the Core algorithm in
`second_level_local_reversal_bridge_by_layout_wf_with_env_len`
(`TilingBandScheduleValidator.v:12004-12641`).  Mixed first establishes that the
two points select the same statement and therefore the same band/recipe; it then
repeats endpoint lookup, extended-index splitting, domain-completeness tile
reconstruction, root/child tile evaluation, target schedule decomposition, and
the final lexicographic reversal argument.

The right abstraction is a new Core pair-local second-level bridge, parallel to
the existing ordinary pair-local bridge at
`TilingBandScheduleValidator.v:11131`.  It should take pair-local compatibility
premises for the selected bands/recipes.  Two existing callers can then supply
them differently:

- the uniform Core route derives them from `common_second_level_recipe_sizes`
  and `common_band_start`;
- the mixed route derives them from same-statement equality.

This keeps the current mixed theorem name and type as a short compatibility
facade while removing roughly five hundred duplicated proof lines from this
file.

## Dead compatibility route

The three declarations outside the repository's external-root closure are:

- `unique_phase_schedules_identify_statement` (`490-521`);
- `phase_separated_ordinary_reversal_same_statement` (`1564-1834`);
- `phase_separated_ordinary_local_reversal_bridge_wf_with_env_len`
  (`2225-2767`).

The last two form the older ordinary route: unique phases force the same
statement, followed by a fully inlined ordinary band proof.  The active route
is less restrictive and better factored: equal phase implies compatible class,
then Core's ordinary pair bridge does the band argument.  Do not polish the old
502-line proof.  Either preserve its name with a short wrapper over the current
Core bridge, or remove the three declarations after an explicit external-API
decision.

## Ownership and reusable lemmas

- Seven schedule-head definitions/lemmas are duplicated nearly verbatim in
  `TilingBandPhaseScalarValidator.v`: `schedule_head_constant`,
  `pinstr_head_constant`, `forallb_zeqb_zero_dot_product`,
  `schedule_head_constant_sound`, `forallb_skipn_true`,
  `schedule_head_constant_lift`, and `schedule_head_constant_lift_sound`.
  Move them to one phase-schedule support functor below both validators; retain
  old paths by thin definitions/theorem wrappers if compatibility matters.
- `NoDup_nth_error_injective_local` is generic.  An equivalent theorem already
  exists as `ISSRefinement.NoDup_nth_error_injective` at
  `ISSRefinement.v:600`.  Put one version in `Misc.v` or a small list-facts
  module (both clients can depend downward on it) and keep compatibility
  wrappers if needed.
- `z_not_inb`, `z_nodupb`, and their soundness proofs are generic Boolean facts
  over `list Z`; they do not belong to band semantics.  They may move to a
  low-level Z-list facts module, though this has lower payoff than the bridge
  extraction.
- `second_level_recipe_links_length` belongs beside
  `Core.second_level_band_recipe_spec_lengths`.
- `grouped_second_level_expected_timestamp_prefix` and
  `ordinary_stripmine_expected_timestamp_prefix` are schedule representation
  lemmas and belong in Core beside the constructors/evaluation theorems they
  describe.
- The phase-class consistency scanner is structurally similar to the
  phase-scalar scanner but carries different payload invariants.  Do not begin
  with a higher-order generic scanner; it would complicate statements for a
  small line reduction.  First share only the exact schedule-head block.

## Facade and module-boundary issue

`TilingBandPhaseScalarValidator.v` instantiates
`TilingBandMixedSecondValidator PolIRs` only to write `Module Core := Mixed.Core`;
there is no other `Mixed.` use in that file.  `TilingBandDirectRuntime.v` then
obtains Mixed through `Module Mixed := PhaseScalar.Mixed` and Core through
`Module Legacy := Mixed.Core`.  This couples and nests three large functors for
module-path convenience, not theorem dependency.

The dependency-clean form is:

- PhaseScalar instantiates `TilingBandScheduleValidator PolIRs` directly;
- DirectRuntime instantiates PhaseScalar and Mixed independently;
- DirectRuntime obtains Legacy/Core directly from ScheduleValidator (or from
  Mixed only if retaining that alias is useful).

Removing `PhaseScalar.Mixed` changes an externally visible nested module path.
Keeping that alias also keeps the Mixed instantiation, so API preservation and
compile-time reduction conflict here.  Measure the direct-import prototype in
a throwaway branch/worktree and make an explicit compatibility decision; do not
silently change the path.

## Low-risk refactor order

1. Add only section headings and stage comments to the two live correctness
   facades and the two live phase arguments.  No theorem changes.
2. Replace the dead 502-line ordinary proof with a wrapper over Core's existing
   pair-local ordinary bridge, preserving its public declaration.
3. Introduce the Core pair-local second-level bridge; refactor Core's existing
   uniform theorem to call it; then reduce Mixed's 586-line theorem to an
   adaptor.  Preserve all existing theorem names and statements.
4. Extract the one-endpoint observation helper(s) as `Local` declarations to
   shorten `mixed_second_level_reversal_same_statement` and
   `phase_separated_ordinary_reversal_same_class`.
5. Deduplicate exact schedule-head support and generic list facts behind
   compatibility wrappers.
6. Only after proof/API tests, prototype the direct functor imports in
   PhaseScalar and DirectRuntime.

## Measurable prototype

For each structural step, compare a clean baseline with the prototype using the
same container and job count:

1. clean full build wall time and peak RSS;
2. isolated compilation time and peak RSS for
   `TilingBandScheduleValidator.vo`, `TilingBandMixedSecondValidator.vo`,
   `TilingBandPhaseScalarValidator.vo`, and `TilingBandDirectRuntime.vo`;
3. incremental rebuild after touching only Mixed, then only PhaseScalar;
4. `.vo` sizes and `coqdep` predecessor counts;
5. full existing test suite and current CI-equivalent `coqc` build.

The bridge extraction is primarily a readability/maintenance improvement and
may not reduce Core compilation time; the direct-functor prototype is the step
that can reduce redundant elaboration and downstream incremental recompilation.
Do not add or use `coqchk`; the project acceptance gate is the clean full
`coqc` build plus existing CI/tests.

## Bottom line

The current active proof is substantively the intended direct permutable-band
pipeline.  Its main readability defect is architectural duplication: the
ordinary mixed route delegates band semantics to a Core pair-local bridge,
while the mixed second-level route inlines nearly the same Core algorithm.  Fix
that ownership mismatch first.  The checker facades themselves are soundly
layered and should remain visible as the public entry points.

---

# Long-proof audit: `TilingBandMixedSecondValidator.v`

Scope: every proof with at least 30 lines from `Proof.` through `Qed.` in the
current `proof/readability-cleanup` worktree.  "Live" means reachable from one
of the six declarations used, by qualified name, in
`TilingBandDirectRuntime.v`; it is not a claim about downstream clients outside
this repository.

## 1. `mixed_second_level_reversal_same_statement`

- Span: `617-908`; proof: `654-908` (255 lines); live.
- Purpose: under unique scalar phases and the grouped second-level schedule
  shape, an old-order reversal that is not a new-order reversal must concern
  two dynamic instances of the same source statement.
- Ownership: the phase-to-statement argument is specific to this mixed
  validator.  The schedule-prefix normalization belongs lower, with the
  second-level schedule representation in `TilingBandScheduleValidator.v`.
- Why long: the proof independently recovers the statement, witness, band and
  recipe for each endpoint (`671-741`), reconstructs the expected grouped
  target timestamp (`742-833`), transports target nondecrease to that form
  (`834-865`), then obtains equality of the preserved one-element phase prefix
  and uses phase uniqueness (`866-907`).  The mathematical argument is short;
  most lines unpack the two endpoint observations symmetrically.
- Low-risk extraction: define a `Local` one-endpoint observation lemma just
  before line 617.  For a member of the flattened program, it should return the
  source instruction/witness/band/recipe facts plus an equation
  `target_ts = firstn 1 source_ts ++ rest` and the evaluation of that one-element
  prefix.  Replace `671-833` and `866-892` with two calls.  Keep the public
  theorem and its statement unchanged.
- Stage comments if extraction is postponed: before `671` (recover endpoint
  metadata), `778` (normalize source and target timestamps), `834` (transport
  target nondecrease), and `894` (phase equality identifies the statement).

## 2. `mixed_second_level_local_reversal_bridge_wf_with_env_len`

- Span: `910-1538`; proof: `953-1538` (586 lines); live.
- Purpose: turn a reversed pair into the common-band slice and decreasing-band
  component needed by the componentwise permutable-band soundness theorem.
- Ownership: only `959-964`, which obtains same-statement equality from the
  mixed phase policy, belongs in this file.  The remaining point decomposition,
  tile reconstruction, schedule decomposition, and lexicographic argument are
  the generic second-level band bridge.
- Why long: after same-statement equality, the proof repeats the algorithm of
  `Core.second_level_local_reversal_bridge_by_layout_wf_with_env_len`
  (`TilingBandScheduleValidator.v:12004-12641`): endpoint lookup (`965-1042`),
  structure and timestamp facts (`1043-1195`), domain-completeness recovery of
  tile coordinates (`1196-1225`), root/child tile reconstruction (`1226-1291`),
  band-row and timestamp splitting (`1292-1361`), expected grouped target
  timestamps (`1362-1440`), and the final reversal-to-decreasing-component
  argument (`1441-1537`).  This is duplicated semantic machinery, not
  irreducible mixed-case complexity.
- Preferred refactor: add a pair-local second-level bridge in
  `TilingBandScheduleValidator.v`, parallel to
  `ordinary_pair_local_reversal_bridge_wf_with_env_len` at line 11131.  It
  should accept callbacks or premises that establish, for the selected pair,
  compatible/equal band start and length and equal root/child recipe sizes (or
  the equivalent band/recipe equalities), together with the layout schedule
  premise.  The existing Core program-wide theorem supplies these facts from
  `common_second_level_recipe_sizes` and `common_band_start`; this mixed theorem
  supplies them from same-statement equality.  The public theorem here then
  becomes a short adaptor like the ordinary wrapper at `2151-2223`.
- Avoid extracting many tiny local lemmas from the 586-line body first.  That
  would preserve the cross-file duplication and obscure ownership.
- Stage comments if the Core extraction is deferred: before `959`, `974`,
  `1043`, `1068`, `1196`, `1226`, `1292`, `1310`, `1362`, `1429`, `1473`, and
  `1509`.

## 3. `phase_separated_ordinary_reversal_same_statement`

- Span: `1564-1834`; proof: `1599-1834` (236 lines); not live in this repo.
- Sole caller: the likewise unreachable old bridge at `2225-2767`.
- Purpose: an older, stronger ordinary-layout route used globally unique phases
  to force equal source-statement indices.
- Ownership: phase logic belongs here; ordinary strip-mine timestamp
  normalization belongs in Core.
- Recommendation: do not spend readability effort inside it.  Mark the pair of
  old declarations as a compatibility route, or remove them only after an
  explicit external-API decision.  If retained and revived, reuse the same
  endpoint-observation helper proposed for proof 1, parameterized by the
  expected target-prefix normalization.
- Useful stage comments only if retained as active documentation: before
  `1616`, `1620`, `1638`, `1695`, `1726`, `1760`, and `1820`.

## 4. `phase_separated_ordinary_reversal_same_class`

- Span: `1836-2149`; proof: `1877-2149` (273 lines); live.
- Purpose: show that a reversed pair has equal phase and therefore, by the
  phase-class consistency check, the same ordinary band and tile-size recipe.
  Unlike proof 3, it deliberately permits different statements in one phase
  class.
- Ownership: this is the central ordinary mixed-class lemma and belongs here.
  The generic schedule-prefix decomposition does not.
- Why long: it performs symmetric lookup of instructions, witnesses, bands and
  class entries (`1883-1967`), recovers the two strip-mine schedule facts
  (`1968-2031`), transports target nondecrease (`2032-2085`), evaluates and
  equates the phase prefixes (`2086-2134`), then applies class consistency
  (`2135-2148`).  The conceptual proof has four steps but the endpoint
  plumbing is inlined twice.
- Low-risk extraction: add a `Local` ordinary-phase observation lemma before
  line 1836.  For one endpoint it should bundle the entry lookup, band/witness
  lookup, `ptb_start = 1`, schedule match, phase-prefix evaluation, and expected
  target-prefix equation.  Two observations plus
  `preserved_equal_length_prefix_reversal_implies_prefix_eq` leave a short
  class-consistency argument.  Keep the public theorem unchanged.
- Stage comments if extraction is postponed: before `1883` (endpoint
  observations), `1968` (certified strip-mine schedules), `2032` (transport
  target nondecrease), `2086` (recover phase equality), and `2135` (class
  consistency yields band/recipe equality).

## 5. `phase_class_ordinary_local_reversal_bridge_wf_with_env_len`

- Span: `2151-2223`; proof: `2194-2223` (30 lines); live.
- Purpose: adaptor from the phase-class result to Core's pair-local ordinary
  bridge.
- Ownership and quality: correctly placed and already structurally ideal.  It
  first obtains same band/sizes (`2200-2208`), then discharges Core's two
  pair-local callbacks (`2209-2222`).  Do not split it.
- Low-risk readability change: one comment before `2200` and one before `2209`;
  optionally name the two callback facts before the `eapply` if the reader finds
  the nested inversions difficult.  No new exported helper is justified.

## 6. `phase_separated_ordinary_local_reversal_bridge_wf_with_env_len`

- Span: `2225-2767`; proof: `2266-2767` (502 lines); not live in this repo and
  has no caller.
- Purpose: older same-statement ordinary band bridge.
- Ownership: after the same-statement step at `2272-2276`, this duplicates the
  generic Core ordinary pair bridge now used by proof 5.
- Recommendation: do not refactor its body.  If compatibility must be kept,
  replace its proof with `phase_separated_ordinary_reversal_same_statement`
  followed by `Core.ordinary_pair_local_reversal_bridge_wf_with_env_len`, while
  preserving the declaration and module path.  This is lower risk than
  maintaining the inlined copy.  If external compatibility is not required,
  remove it together with proof 3 and the unlifted phase-identification lemma.
- Until that decision, a single header comment saying that this is the legacy
  unique-phase compatibility theorem is more useful than dense internal
  commentary.

## 7. `check_pprog_phase_separated_ordinary_direct_correct_same_ctxt`

- Span: `2843-2933`; proof: `2863-2933` (71 lines); live public root.
- Purpose: top-level executable-checker soundness facade.
- Ownership and quality: correctly placed.  It inverts the checker result
  (`2866-2888`), obtains source/witness facts (`2889-2901`), invokes the common
  tiling correctness theorem (`2902-2916`), turns the executable direct band
  check into a componentwise permutable-band certificate (`2917-2927`), and
  supplies the phase-class bridge (`2928-2932`).
- Recommendation: keep as one proof.  Add four short stage comments at the
  boundaries above.  A higher-order generic checker wrapper would save few
  lines while exposing more impure-checker details to callers.

## 8. `check_pprog_mixed_second_level_direct_correct_same_ctxt`

- Span: `3050-3130`; proof body: `3070-3128` (59 proof lines; the declaration
  parser counts through line 3130 because of the adjacent module end); live
  public root.
- Purpose: top-level executable-checker soundness facade for the mixed grouped
  second-level route.
- Ownership and quality: correctly placed.  It inverts the checker and shape
  evidence (`3073-3083`), obtains source facts (`3084-3096`), invokes common
  tiling correctness (`3097-3111`), proves the componentwise permutable-band
  certificate (`3112-3122`), and supplies the mixed second-level bridge
  (`3123-3127`).
- Recommendation: keep as one proof and add stage comments at those five
  boundaries.  Once proof 2 delegates to a Core pair-local bridge, this facade
  will expose the intended direct-band main chain clearly.

## Priority conclusion

The largest maintainability gain is not local tactic polishing.  It is to make
the second-level architecture match the already-good ordinary architecture:

1. Mixed policy proves pair-local layout compatibility.
2. A Core pair-local bridge proves that reversal yields a decreasing band
   component.
3. The direct checker soundness facade combines that bridge with the proved
   componentwise permutable-band check.

This preserves the current public mixed theorem while eliminating roughly five
hundred lines of duplicated semantic bridge proof.  The active ordinary
phase-class theorem is the model to follow.
