# Read-only audit: small validator facade group

## Scope and method

Audited files:

- `src/TilingCanonicalScheduleValidator.v`
- `src/TilingWitness.v`
- `src/ISSBoolChecker.v`
- `src/ISSValidator.v`
- `src/ISSValidatorCorrect.v`
- `src/ISSWitness.v`

The inventory contains every named top-level Definition, Fixpoint, Lemma,
Theorem, Inductive, and Record in these files.  It records declaration/proof
spans, same-file callers/callees, qualified repository consumers (including
functor aliases split across lines), unique unqualified consumers for the two
global witness files, and intra-file reachability from those consumers.
Comments were excluded.  Reachability is deliberately conservative: “no
repository consumer found” does not mean a public name may be removed.

No repository file was modified and no build was run.

## Inventory

| File | Declarations | Proof bodies | Proof-span lines | Proofs >=30 lines | Reachable from a repository consumer |
|---|---:|---:|---:|---:|---:|
| TilingCanonicalScheduleValidator.v | 14 | 8 | 137 | 2 | 14/14 |
| TilingWitness.v | 62 | 31 | 326 | 1 | 29/62 |
| ISSBoolChecker.v | 36 | 19 | 263 | 1 | 36/36 |
| ISSValidator.v | 13 | 0 | 0 | 0 | 13/13 |
| ISSValidatorCorrect.v | 1 | 1 | 5 | 0 | 1/1 |
| ISSWitness.v | 18 | 7 | 59 | 0 | 8/18 |
| **Total** | **144** | **66** | **790** | **4** | **101/144** |

Complete outputs:

- `/tmp/validator-facades-declaration-audit.csv`: enriched declaration-level
  audit with responsibility, consumers, reachability, priority, risk, and a
  recommendation for all 144 declarations.
- `/tmp/validator-facades-proof-inventory.csv`: raw parser inventory.
- `/tmp/validator-facades-long-proofs.md`: full analysis of all four proofs of
  at least 30 lines.

## Soundness-chain result

### Canonical tiling schedule

The chain is closed:

1. `checked_tiling_schedule_canonical_validate` checks both
   `check_pprog_tiling_sourceb` and exact equality of each target schedule to
   the witness-induced lifted source schedule
   (`TilingCanonicalScheduleValidator.v:178-183`).
2. `check_pprog_tiling_schedule_canonicalb_sound` combines the structural
   certificate with the exact schedule checks to prove that the constructed
   `retiled_old` program equals the submitted target
   (`TilingCanonicalScheduleValidator.v:137-176`).
3. `checked_tiling_schedule_canonical_validate_correct` rewrites target
   semantics by that equality and invokes
   `Tiling.tiling_retiled_old_to_before_instance_correct_source`
   (`TilingCanonicalScheduleValidator.v:196-242`).
4. The outer representation bridge is discharged in
   `checked_tiling_schedule_canonical_validate_outer_correct`, and the public
   poly theorem is consumed by `driver/PolOptCanonicalTiling.v:113`.

No accepted checker fact is dropped.  The problem is duplicated elimination of
the structural checker, not a missing semantic obligation.

### ISS complete-cut route

The chain is also closed:

1. `check_domain_partition_shapeb` checks equal contexts, equal typed variables,
   in-range parent indices, and equality of each child payload apart from its
   domain (`ISSBoolChecker.v:438-474`).
2. `check_domain_partition_cut_shapeb` additionally checks that every child has
   one sign per cut and that its domain is exactly the parent domain extended by
   the selected cut half-spaces (`ISSBoolChecker.v:476-524`).
3. `check_domain_partition_complete_cut_shapeb` additionally checks, for every
   source statement, no duplicated child sign vector and inclusion of every
   expected sign vector (`ISSBoolChecker.v:526-560`).  This establishes
   `Refine.domain_partition_complete_cut_shape`.
4. `checked_iss_complete_cut_shape_validate_semantics_correct` passes that exact
   property to `ISSCutSemantics.iss_complete_cut_shape_to_before_correct`,
   yielding source semantics and final-state equality
   (`ISSValidatorCorrect.v:18-29`, `ISSCutSemantics.v:1206-1212`).
5. This semantic theorem has nine qualified driver call sites across
   `PolOptCorrect`, `PolOptBandTiling`, `ParallelPolOptCorrect`, and
   `PolOptIdentityGenericISS`.

The shape-only and cut-shape `_correct` aliases prove checker-to-property
soundness, not program semantics.  That is intentional: only the complete-cut
route provides the coverage premise required by the semantic theorem.  The
names should be documented because `_correct` alone does not reveal this
distinction.

`ISSValidatorCorrect` currently invokes the underlying ISSBoolChecker soundness
theorem directly instead of the equal public alias already exported by
`ISSValidator`.  This is not a soundness gap, but it weakens the facade boundary.

## Main readability findings

### P0: low-risk cleanup on active proof paths

1. **Stop proving the structural certificate twice in canonical tiling.**
   Add an internal declarative helper from an existing tiling structure relation
   plus canonical schedule checks to `retiled_old = after`.  Keep
   `check_pprog_tiling_schedule_canonicalb_sound` as its current public wrapper,
   and let the semantic endpoint reuse the relation it already has.

2. **Replace anonymous goal-shape automation in ISS.**
   `check_domain_partition_cut_shapeb_sound` reconstructs its shape sub-check
   from hypotheses named `H`, `H4`, `H3`, and `H2`.  Preserve the three outer
   conjuncts and apply the three component soundness lemmas directly.  Apply the
   same explicit naming to the shorter
   `check_domain_partition_shapeb_sound`.

3. **Use the ISS facade in its composition theorem.**
   Replace the direct call to
   `ISSCheck.check_domain_partition_complete_cut_shapeb_sound` by
   `ISSVal.checked_iss_complete_cut_shape_validate_correct`; the theorem type is
   already the intended interface.

### P1: shared utilities, with public wrappers preserved

1. **Context equality is triplicated.**  `ctxt_eqb`, `ctxt_ty_eqb`, and their
   proofs occur independently in ISSBoolChecker, TilingBoolChecker, and
   AffineValidator.  A small Instr-parameterized utility with an iff/spec theorem
   would remove this repetition.  Existing module names should remain aliases or
   wrappers because they are public.

2. **ISS witness/list equality is repetitive and incomplete as an API.**
   ISSWitness implements three list equalities with nearly identical induction,
   but exposes only the true-to-equality direction.  ISSBoolChecker consequently
   proves `iss_halfspace_sign_list_eqb_refl` locally.  Provide one generic list
   equality reflection lemma plus iff/refl facts; retain all concrete public
   definitions and theorem names as wrappers.

3. **TilingWitness duplicates Linalg's dot product.**  The definitions have the
   same truncating behavior, and the app/zero lemmas overlap.  Because
   `TilingWitness.dot_product_app_exact`, split, singleton, and zero lemmas have
   qualified downstream consumers, consolidation should first establish an
   explicit compatibility layer and preserve every existing name.

4. **Two exported sublibraries are dormant inside the repository.**  The
   environment-aware row-lifting/trace branch accounts for much of the 33
   unreached TilingWitness declarations.  The full-cut/full-witness equality
   branch accounts for the 10 unreached ISSWitness declarations.  These are not
   on current validation paths.  Do not spend P0 cleanup effort on them and do
   not delete them while external visibility must remain unchanged.

## Responsibility boundaries

- `TilingWitness.v` should own witness data, tile-parent arithmetic, and minimal
  reusable witness evaluation facts.  Generic dot-product/list algebra belongs
  in Linalg or a dedicated utility layer; dormant trace/access-row APIs should be
  visibly separated by Sections/comments if retained.
- `TilingCanonicalScheduleValidator.v` should own only canonical schedule
  recognition and composition with existing structural/semantic tiling facts.
  It should not repeatedly unpack the structural checker.
- `ISSWitness.v` should own ISS certificate data and equality reflection.
- `ISSBoolChecker.v` should own boolean checks and named reflection proofs from
  each check to the declarative property, not generic list equality machinery.
- `ISSValidator.v` is a compatibility/public facade.  It intentionally contains
  no proofs.
- `ISSValidatorCorrect.v` is the one checker-to-semantics composition point; its
  short theorem is appropriately placed and complete.

## Recommended order

1. Refactor the two canonical P0 proofs through one declarative equality helper.
2. Rewrite the two ISS shape proofs with explicitly named conjunction facts.
3. Make ISSValidatorCorrect consume the ISSValidator soundness alias.
4. Add ISS equality spec/refl support and reduce the local sign-list utilities.
5. Factor shared context equality.
6. Treat dot-product consolidation as a separate, full-build change; leave the
   dormant environment-lifting branch alone unless it is going to be used.


---

# Validator facade audit: proofs of at least 30 lines

Scope: `TilingCanonicalScheduleValidator.v`, `TilingWitness.v`,
`ISSBoolChecker.v`, `ISSValidator.v`, `ISSValidatorCorrect.v`, and
`ISSWitness.v` in the `proof/readability-cleanup` worktree snapshot audited on
2026-08-07.  Proof span counts include `Proof.` and the closing command.

There are four proofs of at least 30 lines (153 proof-span lines total).

## 1. `check_pprog_tiling_schedule_canonicalb_sound`

- File/lines: `src/TilingCanonicalScheduleValidator.v:137-176`
- Proof span: 31 lines (`Proof.` at 146)
- Public reachability: internal on the repository-consumed canonical tiling
  path.  Its caller is `checked_tiling_schedule_canonical_validate_correct`.
- What it proves: given the structural tiling-source checker and the canonical
  schedule checker, the program obtained by replacing every source instruction
  with `retiled_old_pinstr` is definitionally the submitted target program.
- How it works: destruct both program triples; reflect context and typed-variable
  equality; invoke `check_pprog_tiling_sourceb_sound` to recover the per-
  instruction structural relation; align compiled and source witnesses with
  `compiled_pinstr_tiling_witness_Forall2`; then apply the list equality lemma.
- Why it is long: this is certificate plumbing, not a difficult tiling theorem.
  It eliminates the structural boolean result here even though the semantic
  endpoint has already eliminated the same result.
- Recommended rewrite: add an internal helper whose premises are the already
  obtained declarative program structure relation plus the schedule boolean and
  whose conclusion is the `retiled_old` program equality.  Keep this theorem's
  public name and type as a wrapper.  Risk: low; priority: P0.

## 2. `checked_tiling_schedule_canonical_validate_correct`

- File/lines: `src/TilingCanonicalScheduleValidator.v:196-242`
- Proof span: 38 lines (`Proof.` at 205)
- Public reachability: core semantic theorem; reached by
  `checked_tiling_schedule_canonical_validate_outer_correct`, then by
  `checked_tiling_schedule_canonical_validate_poly_correct`, which is consumed
  at `driver/PolOptCanonicalTiling.v:113`.
- What it proves: acceptance of the structural and canonical-schedule checks,
  together with target instance-list semantics, yields source instance-list
  semantics and `State.eq` final states.
- How it works: split the accepted conjunction; obtain the complete structural
  certificate (relation, statement identities, witness well-formedness, positive
  tile sizes, and depths); unpack the relation to substitute context/variable
  equality; reconstruct the same program relation; call the preceding equality
  theorem; rewrite target semantics to `retiled_old`; finish with
  `tiling_retiled_old_to_before_instance_correct_source`.
- Why it is long: one semantic step is surrounded by repeated certificate
  unpacking/repacking.  In particular, the call at lines 235-238 causes
  `check_pprog_tiling_sourceb_sound` to be used a second time inside the helper.
- Recommended rewrite: retain one named certificate bundle, pass its declarative
  relation to the new equality helper, and apply the semantic theorem directly.
  Preserve all theorem names/statements.  Risk: low; priority: P0.

## 3. `dot_product_insert_zeros_at`

- File/lines: `src/TilingWitness.v:319-374`
- Proof span: 49 lines (`Proof.` at 326)
- Public reachability: no repository consumer was found for this theorem or the
  environment-aware row-lifting branch that calls it.  It remains an exported
  API and must not be deleted or renamed.
- What it proves: inserting a block of zero coefficients after an environment
  prefix does not change a truncating dot product when the value vector receives
  a matching middle block.
- How it works: establish the `firstn` length, reassociate coefficient and value
  lists, split the dot product twice, eliminate the zero block, manually prove a
  second prefix/suffix split for the original dot product, then solve arithmetic.
- Why it is long: the available `dot_product_split_firstn_skipn` lemma requires
  exact total lengths, while this theorem intentionally assumes only that the
  environment prefix fits inside the coefficient list.  Therefore lines 355-370
  rebuild the more general prefix split locally.
- Existing-library overlap: `TilingWitness.dot_product` has the same truncating
  definition as `lib/Linalg.v:294-298`; `dot_product_app_exact` duplicates
  `Linalg.dot_product_app` (`lib/Linalg.v:372-378`), and the zero lemmas overlap
  `lib/Linalg.v:359-370`.  Several surrounding TilingWitness lemmas have
  qualified downstream users, so wholesale replacement is not a local edit.
- Recommended rewrite: first add a general prefix-splitting helper with premises
  `length prefix = n` and `n <= length coeffs`; use it to remove the local
  `Hsplit` block.  Separately, consider making the public TilingWitness dot-
  product lemmas wrappers over Linalg after proving compatibility and running a
  full build.  Risk: medium; priority: P1.

## 4. `check_domain_partition_cut_shapeb_sound`

- File/lines: `src/ISSBoolChecker.v:486-524`
- Proof span: 35 lines (`Proof.` at 490)
- Public reachability: internal on the complete-cut checker path.  It is consumed
  by `check_domain_partition_complete_cut_shapeb_sound`, which is used by the
  final semantic endpoint.
- What it proves: acceptance of the ISS cut-shape boolean establishes the three
  declarative clauses: basic parent/payload shape, per-piece sign-vector
  well-formedness, and domains equal to the parent domain plus selected cut
  half-spaces.
- How it works: broad `simpl` and repeated goal-shape matching flatten all nested
  booleans; the proof then reconstructs the original shape boolean using
  anonymously generated hypotheses `H`, `H4`, `H3`, and `H2`; finally it invokes
  the three component soundness lemmas.
- Why it is long: no theoretical difficulty.  The target-shape tactic destroyed
  the useful abstraction boundary and forced the proof to rebuild it.  The
  numbered hypotheses are especially brittle under any checker-clause change.
- Recommended rewrite: reduce only the outer program destructors, retain
  `check_domain_partition_shapeb ... = true` as a named conjunct, destruct the
  three outer `andb` facts explicitly, and apply the three component soundness
  theorems.  Risk: low; priority: P0.

## Long-proof conclusion

Three of the four long proofs are composition/list-shape artifacts and can be
made substantially shorter without changing a definition or theorem statement.
The fourth (`dot_product_insert_zeros_at`) reflects a real mismatch between a
weak prefix-bound premise and the stronger list-splitting helper, but it is on a
currently unconsumed exported branch and should follow the P0 facade cleanups.
