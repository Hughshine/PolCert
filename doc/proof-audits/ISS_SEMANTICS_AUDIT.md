# Read-only audit summary: `ISSSemantics.v`

## Scope and results

- Worktree: `work/proof-readability`, branch `proof/readability-cleanup`.
- Source: 626 lines, 28 declarations, 21 proofs, one `Local` lemma.
- Long proofs: three at or above 30 proof lines; two are live central theorems,
  one belongs to a dead route.
- Qualified external roots: nine declarations, all used from
  `ISSCutSemantics.v`.
- Repository-live closure: 21 declarations (nine roots and 12 dependencies).
  Seven declarations lie outside it.
- Generated artifacts:
  - `/tmp/iss_semantics_declarations.csv`: every declaration with source/proof
    spans, dependencies, internal callers, external qualified uses,
    root/closure status, tactic counts, ownership, and action.
  - `/tmp/iss_semantics_long_proofs.md`: manual review of all three proofs of at
    least 30 proof lines, including exact stage/comment points.

The reachability result is repository-local.  Except for one `Local` lemma, all
declarations are exported by the functor, so removing an unused declaration is
still an external API decision.

## What the file proves

The active construction maps a flattened target instance back to its source
parent by changing only its statement number:

1. `set_ip_nth` replaces the statement index and preserves the point, schedule,
   transformation, instruction, and depth fields.
2. `before_parent_nth` reads an after statement's parent from its ISS witness.
3. `before_of_after_point` and `before_ipl_from_after` apply that relabeling to
   one target point or a complete flattened list.
4. The small preservation lemmas show that relabeling does not change point
   execution or its timestamp.
5. `before_ipl_from_after_forward` proves that every mapped point is a valid
   source-program instance.
6. `before_ipl_from_after_backward` proves that every valid source instance is
   represented by the mapped target list, using coverage of each source domain
   by its ISS children.

`ISSCutSemantics.v` then uses the forward/backward membership characterization
to build a source flattened list, prove its uniqueness/order properties, map
the target execution trace back to source points, and obtain semantic
equivalence.  Thus this file's real public contribution is a representation
theorem for the after-to-before instance map, not the cut-specific semantics
itself.

## Public roots

The nine declarations used by qualified name in `ISSCutSemantics.v` are:

- `set_ip_nth` and `before_parent_nth` (one unfolding site each);
- `before_of_after_point` (four uses);
- `before_ipl_from_after` (six uses);
- `point_semantics_before_of_after_preserved` (one use);
- `before_of_after_point_time_stamp_preserved` (one use);
- `nth_error_combine_local` (three uses);
- `before_ipl_from_after_forward` (three uses);
- `before_ipl_from_after_backward` (one use).

The first six and last two form the semantic API.  The combine lemma is a
generic list compatibility artifact and should not be conceptually part of the
ISS semantics API.

## Dead alternative route

Seven declarations are outside the live closure:

- `find_after_stmt_index`;
- `after_of_before_point`;
- `after_ipl_from_before`;
- `point_semantics_after_of_before_preserved`;
- `after_of_before_point_time_stamp_preserved`;
- `find_after_stmt_index_sound`;
- `NoDupA_np_implies_NoDup`.

The first six are an alternative before-to-after search design.  They scan the
after statements for the first child with the requested parent whose domain
contains the point.  The file proves only that a successful lookup identifies a
matching child.  It does not prove lookup completeness from partition coverage,
uniqueness from disjointness, or that `after_ipl_from_before` is a flattened
target list.  The active end-to-end proof instead maps after points to parents
and proves backward membership existentially.  Therefore this is an unfinished
and unused design branch, not a second part of the active theorem chain.

`NoDupA_np_implies_NoDup` is unrelated to that search but is also unused.  The
actual construction in `ISSCutSemantics.v` needs the converse-shaped result:
ordinary `NoDup` plus uniqueness under `np_eq` implies `NoDupA np_eq`.

Recommended policy: remove these seven declarations if no external compatibility
is promised.  Otherwise isolate the search block under an explicit
"alternative search API" section and avoid spending time optimizing its proof.

## Ownership findings

### Refinement facts are in the semantics file

Nine declarations merely project or connect definitions owned by
`ISSRefinement.v`:

- `payload_eq_except_domain_implies_depth`;
- the two `payload_eq_except_domain_transfer_belongs_to*` lemmas;
- `stmt_partition_refinement_payload_of_child`;
- `stmt_partition_refinement_subset_of_child`;
- `domain_partition_refinement_parent_stmt`;
- `parent_witnesses_in_range_nth`;
- `nth_error_after_stmt_implies_child`;
- `child_in_children_for_parent_inv`.

Move them to `ISSRefinement.v` or, preferably if incremental rebuild boundaries
matter, a small `ISSRefinementFacts.v` that imports only `ISSRefinement.v` and
is shared by `ISSSemantics.v` and `ISSCutSemantics.v`.  The acyclic dependency
would be:

`ISSRefinement -> ISSRefinementFacts -> ISSSemantics -> ISSCutSemantics`.

This is not merely cosmetic.  `ISSCutSemantics.v` independently defines
`nth_error_after_stmt_implies_child_pair`, the pair-valued version of the child
correspondence.  One shared parent/child pair lemma in the refinement facts
layer can derive both the pair and projected-child results.

The two payload-transfer proofs are mirror images with 20 and 19 proof lines.
Add symmetry/projection lemmas for `payload_eq_except_domain` and prove one
generic transport result, then preserve the current theorem names as wrappers.
The current long nested conjunction makes every consumer unfold and destruct
the full payload definition.

### Generic list facts already exist lower in the graph

`nth_error_combine_local` duplicates one direction of
`Misc.nth_error_combine` (`Misc.v:167`).  Its 13-line induction can become a
one- or two-step wrapper, preserving the path currently used by
`ISSCutSemantics.v`.  `in_combine_nth_error_local` can likewise be proved by
`In_nth_error` followed by `Misc.nth_error_combine`; its private induction is
unnecessary.

### A flattening fact is misplaced in Extractor

The backward theorem imports and instantiates the entire Extractor functor only
to call `Extractor.flatten_instrs_in_intro` at line 611.  That lemma is a direct
projection of the `PolyLang.flatten_instrs` definition and contains no
extraction-specific premise.  It belongs in `PolyLang.v` (with an Extractor
compatibility wrapper if needed).  Once moved, `ISSSemantics.v` can drop its
Extractor dependency.

## Module and import structure

The file has no section headings or proof map, so active and dead constructions
appear as one sequence.  Suggested reader-level sections are:

1. after-to-before point relabeling;
2. relabeling invariance;
3. refinement/parent-child facts;
4. flattened-list representation theorem;
5. alternative before-to-after search, only if retained.

Static inspection also finds:

- `Module TileRel := TilingRelation Instr` is never used;
- `Module State := PolIRs.State` is never used;
- `Sorting.Permutation`, `Sorting.Sorted`, and `SelectionSort` have no use in
  this file;
- `SetoidList` is used only by the dead `NoDupA_np_implies_NoDup` theorem;
- `Extractor` is used only for the misplaced flatten-membership introduction
  lemma.

After moving that lemma and deciding the dead API, remove the unused module
applications/imports one at a time and verify with a clean `coqc` build.  In
particular, eliminating the unused `TilingRelation` functor application and the
single-use Extractor functor application is more likely to improve elaboration
and incremental build behavior than changing any tactic in the live proofs.
`Base` and `Linalg` also have no obvious qualified occurrence, but their removal
should be treated as a compile-tested import cleanup because they may provide
unqualified notation or transitive facts.

## Long proofs and intrinsic complexity

- `find_after_stmt_index_sound`: 34 proof lines, simple induction, dead route.
- `before_ipl_from_after_forward`: 86 proof lines, central and logically linear;
  length comes from recovering aligned after/witness/source records.
- `before_ipl_from_after_backward`: 61 proof lines, central cover-witness
  construction; already names its important intermediate facts.

Neither live proof uses expensive automation.  They use bounded destructuring,
named assertions, direct rewrites, and at most small `eauto` calls.  Tactic
replacement will not materially improve compilation.  Their readability would
improve most by stating one public iff theorem:

`In ip (before_ipl_from_after stmt_ws ipl_after)` iff `ip` has a source
instruction, the environment prefix, source membership, and the expected index
length.

Make the existing `forward` and `backward` declarations thin projections of
that theorem so all current callers and paths remain valid.

## Low-risk refactor order

1. Add a proof map and section headings; add stage comments to the two live long
   proofs.  No signature changes.
2. Replace both combine inductions with wrappers around
   `Misc.nth_error_combine`.
3. Move `flatten_instrs_in_intro` down to `PolyLang.v`, retain its Extractor
   wrapper, and switch this file to the lower theorem.
4. Consolidate parent/child and payload projection lemmas in
   `ISSRefinementFacts.v`; keep compatibility wrappers where paths may matter.
5. Introduce `before_ipl_from_after_spec` and make the current directional
   theorems wrappers.
6. Decide whether the seven dead declarations are supported API.  Remove them
   or isolate them; do not locally optimize them first.
7. Remove unused heavy imports/module applications and compare clean and
   incremental build times.

## Bottom line

The active proof is conceptually clean: ISS partitions change statement
identity and domain, while each dynamic target point maps to the same source
operation by replacing only its statement number.  The file's difficulty is
not proof search.  It is blurred ownership: generic list facts, refinement
projections, an Extractor-independent flatten lemma, an unused TilingRelation
instance, and an unfinished reverse-map design all surround two straightforward
representation theorems.  Fixing those boundaries will make the proof much
shorter to read and can also reduce unnecessary compilation dependencies.

---

# Long-proof audit: `ISSSemantics.v`

Scope: every proof with at least 30 lines from `Proof.` through `Qed.` in the
current `proof/readability-cleanup` worktree.  "Live" means reachable from an
actual qualified use elsewhere in this repository, principally
`ISSCutSemantics.v`; all non-`Local` declarations remain technically exported.

## 1. `find_after_stmt_index_sound`

- Span: `358-399`; proof: `366-399` (34 lines); outside the repository's live
  external-root closure.
- Purpose: if the executable scan from a source parent/index to an after
  statement returns `n`, recover the after instruction and witness at `n`, the
  parent equality, and domain membership.
- Mathematical complexity: low.  It is a direct induction over `after_pis`
  synchronized with `stmt_ws`.  The head-match case returns index zero; both
  head-mismatch cases recurse and lift the returned index with `S`.
- Readability issue: the recursive result unpack/repack block is duplicated at
  `385-391` and `392-398`.  A local helper for the recursive `option_map S`
  branch, or defining the Boolean head test as a conjunction, would remove the
  duplication.
- Ownership/status: this theorem belongs with the unused before-to-after search
  at `61-172`, not with the active semantics route.  That route has no current
  caller and proves only search soundness, not search completeness or an
  `after_ipl_from_before`/`flatten_instrs` correspondence.  Do not polish this
  proof before deciding whether to retire the entire route.  If compatibility
  requires retention, add a section header describing it as an alternative
  search API and keep the current simple induction.

## 2. `before_ipl_from_after_forward`

- Span: `446-547`; proof: `462-547` (86 lines); live public root, used three
  times in `ISSCutSemantics.v`.
- Purpose: characterize every mapped after instance as a valid source instance:
  it selects a source instruction, retains the environment prefix, satisfies
  source `belongs_to`, and has the source index length.
- Proof stages:
  1. Invert membership in the mapped list to obtain `ip_after` (`467-471`).
  2. Use the `flatten_instrs` characterization to recover its after instruction,
     prefix, membership, and length (`472-476`).
  3. Use partition lengths/range to retrieve its ISS witness and source parent
     (`477-501`).
  4. Show the after instruction is one of that parent's children and project the
     parent's partition refinement (`502-517`).
  5. Transfer payload/domain membership from child to source (`518-529`).
  6. Rebuild the mapped source instruction index, membership, and length
     (`530-546`).
- Mathematical complexity: genuine but modest.  The proof is the forward half
  of the central representation theorem; its length comes from unpacking the
  list/refinement witnesses, not difficult automation or an expensive tactic.
- Ownership issue: five of its helper calls are merely projections or
  correspondence facts for definitions in `ISSRefinement.v`:
  `parent_witnesses_in_range_nth`,
  `nth_error_after_stmt_implies_child`,
  `domain_partition_refinement_parent_stmt`,
  `stmt_partition_refinement_payload_of_child`, and
  `stmt_partition_refinement_subset_of_child`.  Put these in
  `ISSRefinement.v` or a downward `ISSRefinementFacts.v` shared by this file and
  `ISSCutSemantics.v`.
- Low-risk refactor: present this and proof 3 as the two directions of a single
  `before_ipl_from_after_spec` iff theorem.  Preserve the existing `forward`
  declaration as a one-direction wrapper.  Within the proof, add stage comments
  before lines `467`, `472`, `477`, `502`, `509`, `518`, and `530`.  A large
  opaque helper is not warranted; the stages are the argument readers need to
  see.
- Tactic audit: five named `assert`s, seven `destruct`s, six `eapply`s, two
  `lia`s.  No broad `eauto`, `repeat`, or expensive search drives the proof.
  Replacing tactics is unlikely to change compile time materially.

## 3. `before_ipl_from_after_backward`

- Span: `549-626`; proof: `564-624` (61 lines); live public root, used once in
  `ISSCutSemantics.v`.
- Purpose: completeness of the representation.  Every valid source instance is
  the mapped image of some after child instance.
- Proof stages:
  1. Project the selected parent's partition refinement (`569-579`).
  2. Use domain coverage to choose a child containing the source point and
     recover its payload equality (`580-586`).
  3. Invert child-list membership to obtain aligned after/witness indices
     (`587-590`).
  4. Change only the statement index, then transfer `belongs_to` and index
     length to the chosen child (`591-608`).
  5. Introduce that point into the after flattened list and map it back to the
     source point (`609-623`).
- Mathematical complexity: this is the substantive completeness direction but
  remains a direct cover-witness construction.  The proof is already linear
  and names its intermediate facts well.
- Important dependency issue: line `611` uses
  `Extractor.flatten_instrs_in_intro`, but that theorem (`Extractor.v:2140`) is
  just the reverse projection of the definition
  `PolyLang.flatten_instrs` (`PolyLang.v:2005-2035`) and contains no extraction
  fact.  Move it to `PolyLang.v` (retaining an Extractor wrapper if needed) so
  `ISSSemantics.v` can drop its large Extractor functor dependency.
- Low-risk refactor: make this the reverse half of
  `before_ipl_from_after_spec`, retaining the old theorem as a wrapper.  Add
  stage comments before `569`, `580`, `587`, `591`, and `609`.  Do not hide the
  domain-cover choice or the final flattened-list introduction behind a single
  helper; those are the semantic insight.
- Tactic audit: four named `assert`s, four `destruct`s, three `eapply`s, no
  `lia`, `eauto` search, or repeated unfolding beyond the final map
  normalization.  It is not a tactic-performance problem.

## Long-proof conclusion

Only the two directional representation proofs are live and materially
important.  They are not intrinsically too long, and their tactics are already
predictable.  The readability gain comes from exposing them as one iff
specification and moving definition-projection facts to the refinement layer.
The sole long dead proof belongs to an unused alternative mapping route and
should not receive local cleanup before that route's API status is decided.
