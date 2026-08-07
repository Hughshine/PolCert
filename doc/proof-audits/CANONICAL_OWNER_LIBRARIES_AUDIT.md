# Canonical-owner audit: `Misc`, `ListExt`, `Linalg`, `LinalgExt`, and `InstanceListSema`

## Scope and artifacts

Read-only audit of:

- `lib/Misc.v` (944 lines; 104 named declarations, including 7 Ltac declarations)
- `lib/ListExt.v` (878 lines; 50 declarations)
- `lib/Linalg.v` (1,946 lines; 220 declarations, including 3 executable examples)
- `lib/LinalgExt.v` (528 lines; 4 declarations)
- `polygen/InstanceListSema.v` (397 lines; 23 declarations inside `ILSema`)

Across the five files, the inventory has 401 named declarations and nine
proofs with at least 30 proof lines.  The per-declaration CSVs include source
and proof spans, internal dependencies/callers, external token and qualified
uses, reachability classification, semantic role, canonical owner, and action:

- `/tmp/misc_declarations.csv`
- `/tmp/list_ext_declarations.csv`
- `/tmp/linalg_declarations.csv`
- `/tmp/linalg_ext_declarations.csv`
- `/tmp/instance_list_sema_declarations.csv`

The corresponding long-proof reports are:

- `/tmp/misc_long_proofs.md`
- `/tmp/list_ext_long_proofs.md`
- `/tmp/linalg_long_proofs.md`
- `/tmp/linalg_ext_long_proofs.md`
- `/tmp/instance_list_sema_long_proofs.md`

The CSV inventory treats named definitions, fixpoints, inductives, records,
lemmas/theorems, instances, examples, and Ltac declarations as declarations.
It does not list imports, scopes, hints, notation declarations, constructors,
or the `ILSema` container itself.  In particular, the eight `case_if` tactic
notation overloads in `Misc.v:419-457` are discussed but are not CSV rows.

Reachability is lexical and conservative.  A unique qualified use is strong
evidence; an unqualified use of a colliding name is only a candidate.  No-token
use does not rule out external clients, notation expansion, typeclass search,
or generated module paths.

## Acyclic ownership boundary

The relevant import direction is:

```text
Misc
  -> ListExt
      -> Linalg
          -> LinalgExt
              -> PolyBase
                  -> InstanceListSema.ILSema
                      -> PolyLang and validators
```

`Linalg` imports both `Misc` and `ListExt`; `LinalgExt` imports `Linalg` and
`Misc`; `PolyBase` imports both linear-algebra modules; `InstanceListSema`
imports `PolyBase`, `Linalg`, and `LinalgExt`.  This validates three separate
canonicalization layers:

1. generic map/combine/`Forall2` facts in `Misc`, with `NoDup`/setoid-list and
   richer structural facts in `ListExt`;
2. linear algebra and polyhedron facts in `Linalg`/`LinalgExt`;
3. instruction-point semantic facts in `InstanceListSema.ILSema`.

Do not put a `lex_compare` fact in `ListExt`: `lex_compare` is defined in
`Linalg`, which already imports `ListExt`, so that would create a cycle.

## Planned families: what already exists and what is missing

### Map, combine, `Forall2`, and `NoDup`

| Family | Existing canonical fact | Gap and final owner | Compatibility paths |
|---|---|---|---|
| Map lookup inversion/forward | `Misc.nth_error_map_iff` (`128-138`) | Add named directional corollaries in `Misc` | Keep `Extractor.nth_error_map_inv`, `ParallelValidator.nth_error_map_inv`, `TilingValidator.nth_error_map_inv`, `ISSRefinement.nth_error_map_some/inv`, and `TilingRelation.nth_error_map_some` as wrappers. |
| Paired combine lookup | `Misc.nth_error_combine` (`167-177`) | Exact-index iff already exists. Add only a named existence/membership corollary if required. | Keep ISS local names as wrappers. |
| One-sided `Forall2` lookup | `Misc.Forall2_nth_error` (`260-267`) returns an existential matching right element | Add exact-index corollary accepting both lookup equations in `Misc` | Keep `TilingRelation.Forall2_nth_error` (`151-167`) and `ISSCutSemantics.Forall2_nth_error_local` (`439-456`) as wrappers. |
| `NoDup_map_on` | No fact in `Misc` or `ListExt` | Add in `ListExt` | Exact duplicates are `TilingRelation.v:105-137` and `ISSCutSemantics.v:37-69`. |
| Equal lookups imply equal indices under `NoDup` | No fact in `Misc` or `ListExt` | Add `NoDup_nth_error_injective` in `ListExt` | Keep `ISSRefinement.v:600-615` and `TilingBandMixedSecondValidator.v:476-488`. |
| `NoDup (map f xs)` implies value-level injectivity | No fact in `Misc` or `ListExt` | Add in `ListExt` | Keep `ISSCutSemantics.NoDup_map_value_unique` (`331-361`). |
| Filtered index uniqueness | No fact in `Misc` or `ListExt` | Add a generic theorem in `ListExt`, probably derived from filtered-position/order facts rather than copying the induction | Keep `ISSCutSemantics.NoDup_filter_nth_error_unique` (`389-437`). |
| `NoDup` to `NoDupA` under relation uniqueness | No fact in `ListExt` | Add in `ListExt` (requiring only the standard `SetoidList` import) | Keep `ISSCutSemantics.NoDup_np_eq_unique_implies_NoDupA` (`888-918`). |

`Misc` is already the correct low-dependency owner for the map/combine and
`Forall2` primitives.  It should not acquire `ListExt` as an import.  `ListExt`
has no `NoDup` declaration at all, so the planned `NoDup` APIs are genuine
missing library facts rather than rediscoveries.

### Linear algebra and polyhedron facts

| Family | Existing state | Gap and final owner |
|---|---|---|
| Zero dot products | `Linalg.dot_product_repeat_zero_left/right` (`359-369`) | Already canonical; downstream copies should wrap these. |
| Zero vector and vector negation | `PolyBase.V0`, `Vopp`, `opp_app`, `opp_opp`, `opp_v0_v0` (`323-362`) | They are generic but currently above `LinalgExt`. If lowering is desired, introduce neutrally named implementations in `LinalgExt` and retain every `PolyBase` name/notation as a definition/theorem wrapper. |
| Negated dot product | `PolyBase.dot_product_opp_l/r` (`393-425`) | Generic implementation can move to `LinalgExt`; keep `PolyBase`, `Extractor.dot_product_opp_right` (`751-757`), and `ISSRefinement.dot_product_opp_right_local` (`183-208`) wrappers. |
| One-hot/select coordinate | `PolyBase.v0_n_app_1_dot_product_p_is_nth_p` (`364-374`) | Add one general select-coordinate theorem in `LinalgExt`; preserve `PolyBase` and `ParallelValidator` names. |
| Assignment lookup | `Linalg.assign` and dot-product laws (`1478-1544`), but no pointwise lookup spec | Add `nth`/`nth_error` specification and off-index corollary in `Linalg`; preserve `PolyBase.nth_assign_different`. |
| Polyhedron append | `Linalg.in_poly_app` (`409-413`) | Existing. |
| Polyhedron map/prefix | No `in_poly_map_iff` or generic prefix lift in `Linalg` | Add beside `in_poly`; keep `Extractor.satisfies_constraint_prefix`/`in_poly_prefix` (`1368-1395`) as wrappers or specializations. |
| Matrix width | `Linalg.exact_listzzs_cols` (`948-952`) only | Add head, tail, cons, and append API in `Linalg`; stop consumers unfolding it. |

The current consolidated plan to use `LinalgExt` for zero/negation facts is
acyclic, but it is a physical lowering, not reuse of an existing `LinalgExt`
API.  `LinalgExt` currently contains only four lexicographic theorems.  The
minimal compatibility pattern is:

```text
LinalgExt.vector_zero / vector_opp / generic laws
  -> PolyBase.V0 / Vopp / opp_* / dot_product_opp_* wrappers
      -> Extractor and ISS wrappers
```

This avoids importing `PolyBase` downward and avoids a short-name collision
between a new generic theorem and its existing wrappers.

### Semantic inversion and `eq_except_sched`

`InstanceListSema.ILSema` owns all three definitions that determine the facts:

- `eq_except_sched` (`57-62`);
- `instr_point_sema` (`64-69`);
- `Permutable` (`109-127`);
- plus `instr_point_list_semantics` (`142-150`).

Yet it currently exports only forward list composition
`instr_point_list_sema_concat` (`382-396`) and list-level state-equivalence
stability (`152-175`).  The following are absent and belong here:

1. atomic `instr_point_sema_stable_under_state_eq`;
2. list semantics `nil`, `cons`, `app`, and singleton inversion;
3. both singleton forms needed by existing clients: raw decomposition
   (`exists stmid, point_sema /\ State.eq`) and the state-stabilized direct
   `point_sema` corollary;
4. `eq_except_sched_refl`, `eq_except_sched_symm`, and
   `eq_except_sched_trans`;
5. `instr_point_sema_eq_except_sched_iff`;
6. `permutable_eq_except_sched`.

Verified duplicate locations:

- nil/singleton/app inversion: `Extractor.v:4442-4487`,
  `ParallelLoop.v:499-539`, and `LoopJamNative.v:89-132`;
- cons inversion: `ParallelLoop.v:893` and `LoopJamNative.v:134-145`;
- atomic state stability: `ParallelLoop.v:476-486` and
  `LoopJamNative.v:76-87`;
- semantic and permutability transport:
  `ParallelValidator.v:168-224` and
  `TilingBandScheduleValidator.v:917-997`;
- relation reflexivity/transitivity:
  `AffineValidator.v:3590-3610`.

After adding owner theorems inside the functor, preserve all current paths as
one-line wrappers.  `PolyLang` already aliases `eq_except_sched`
(`1768-1769`) and uses notations for atomic/list semantics and `Permutable`
(`1804`, `1889-1905`), so adding theorem aliases there is acyclic.  Do not
replace public definitions or notations in the same batch.

There is also exact conceptual duplication of `instr_point_sched_le` and its
transitivity proof between `InstanceListSema.v:71-93` and
`PolyLang.v:1812-1834`.  The `ILSema` definition is the natural owner; the
`PolyLang` path can become a compatibility wrapper later.  This is P1 because
it is not required for the requested semantic-inversion canonicalization.

The sorted-list extensionality route
`strongly_sorted_lists_by_timestamp_equal` -> `Sorted_incl_eq` -> two semantic
wrappers (`248-380`) has no current repository token caller.  Keep it outside
the first batch; decide external API/retirement separately.  Repeated imports
at `InstanceListSema.v:195-203` are redundant with the file header and can be
removed independently.

## Long-proof findings

Nine proofs cross 30 proof lines:

| File | Theorem | Proof lines | Recommendation |
|---|---|---:|---|
| `ListExt.v` | `transpose_skipn` | 48 | Keep structure; annotate out-of-range and in-range phases. |
| `ListExt.v` | `ij_error_remove_cols` | 33 | Low-risk shortening via the canonical map lookup corollaries. |
| `ListExt.v` | `transpose_spec` | 56 | Central representation proof; add phase comments, optional small empty-matrix helper. |
| `Linalg.v` | `dot_product_aBp_assoc` | 39 | Genuine algebra; phase comments only. |
| `Linalg.v` | `matrix_product_assoc` | 49 | Add `exact_listzzs_cols` API; retain induction. |
| `LinalgExt.v` | `is_eq_iff_cmp_eq` | 77 | Split directional helpers behind unchanged iff theorem. |
| `LinalgExt.v` | `lex_compare_nil_trans` | 48 | Keep internal bridge; explain comparison cases. |
| `LinalgExt.v` | `lex_compare_trans` | 357 | P0 proof-hygiene refactor: prove Lt once, derive Gt by antisymmetry, isolate Eq. |
| `InstanceListSema.v` | `strongly_sorted_lists_by_timestamp_equal` | 73 | Substantive but currently unreachable route; defer and annotate if retained. |

The 357-line `lex_compare_trans` is the only extreme proof in these canonical
owners.  It has 66 `destruct`s and mirrored strict-order branches.  It is the
clearest candidate for both readability and compile-time measurement.  The
matrix and transpose proofs are structural and should not be generalized merely
to reduce line count.

## Staged refactoring DAG

### Stage A: lowest-risk API additions

```text
Misc named map directions + exact-index Forall2 + combine corollary
  -> ListExt NoDup/NoDupA facts
      -> downstream wrappers in TilingRelation, ISS*, validators, Extractor
```

Compile each owner before wrappers.  This stage does not change executable
definitions or statements.

### Stage B: linear algebra

```text
Linalg exact_listzzs_cols + assign + in_poly APIs
  -> optional LinalgExt neutral zero/negation/select-coordinate API
      -> PolyBase compatibility definitions/theorems
          -> Extractor / ISS / ParallelValidator wrappers
```

The optional lowering of `V0`/`Vopp` should be a separate commit because it
changes the implementation body behind very broad public names, even though
the statements and reduction behavior can be preserved.

### Stage C: semantic owner

```text
InstanceListSema atomic stability + list inversions + eq_except_sched laws
  -> PolyLang theorem aliases
      -> Extractor / ParallelLoop / LoopJamNative / ParallelValidator /
         TilingBand / AffineValidator wrappers
```

This stage has the highest proof-line payoff with low theoretical risk: the
existing copies already demonstrate the facts, and the owner has all required
definitions without importing any client.

### Independent proof-hygiene prototype

Refactor only `LinalgExt.lex_compare_trans` behind its unchanged public
statement.  Measure clean `coqc` time and peak RSS for `LinalgExt.vo`, then one
representative importer, before and after.  This prototype is independent of
the wrapper migration and should not be coupled to it.

## Recommended first implementation batch

1. Add the three `Misc` lookup corollaries and the `ListExt` `NoDup` core.
2. Add `InstanceListSema` atomic stability, list inversions, and
   `eq_except_sched`/permutability transport; turn only exact duplicate clients
   into wrappers.
3. Add `Linalg` width and polyhedron-map facts and use them in
   `matrix_product_assoc` and the smallest downstream duplicates.
4. Separately prototype the `lex_compare_trans` strict-order decomposition.
5. Defer physical `V0`/`Vopp` lowering and the unreachable sorted-list route
   until the smaller batches have clean full-build timing.

All batches must preserve current theorem statements and qualified module
paths.  Validation should use the normal clean `coqc` build and existing CI;
this read-only audit did not run a build.



---

# Long-proof audit: `lib/Misc.v`

No detected `Proof ... Qed` block has 30 or more source lines.  The largest
proof-oriented declaration is the 26-line `reflect_binders` tactic
(`Misc.v:366-391`), not a theorem proof.  The binder-tactic self-tests
`test1`--`test3` (`394-415`) are short; their apparent declaration spans include
the following `Tactic Notation` commands and should not be read as long proofs.

Readability/API notes outside the threshold:

- `nth_error_map_iff` (`128-138`) already proves both map-lookup directions.
  Add named directional corollaries instead of duplicating structural
  inductions downstream.
- `nth_error_combine` (`167-177`) already characterizes a paired lookup at the
  same index.  Only a named membership/existence corollary is missing.
- `Forall2_nth_error` (`260-267`) is one-sided and existential.  It does not
  replace the exact-index theorem used in `TilingRelation` and
  `ISSCutSemantics`; add that theorem beside it.
- The eight `case_if` tactic-notation overloads (`419-457`) and public Ltac API
  are intentionally not proposed for the list-fact canonicalization batch.



---

# Long-proof audit: `lib/ListExt.v`

## `transpose_skipn` (`677`; proof `680-727`, 48 proof lines)

**Purpose.** Shows that dropping the first `n` rows before transposition equals
dropping the first `n` entries of every transposed row, under the rectangular
lower-bound invariant.

**Why it is long.** Lines `682-710` separately establish the out-of-range case
`n > length tapes`: transposing no remaining rows yields `len` empty columns.
Lines `711-726` handle the in-range case through `firstn_skipn`,
`transpose_app`, and the right-identity property of `zipWith`.

**Assessment.** The two cases are semantic, not tactic noise.  Keep the theorem
and add phase comments at `682` and `711`.  A helper for the out-of-range map of
empty lists is possible, but it has no second caller and would obscure the
matrix invariant.  No current external token caller was found; it remains part
of the exported transpose API.

## `ij_error_remove_cols` (`762`; proof `764-796`, 33 proof lines)

**Purpose.** Relates a column offset in a two-dimensional lookup to mapping
`skipn d` over all rows.

**Why it is long.** Lines `766-789` manually split both source and mapped row
lookups into `Some`/`None`, reconstructing the same map-index fact through
length arithmetic.  Lines `790-795` finally use `Misc.nth_error_map_iff`.

**Low-risk refactor.** Use a named forward/inversion corollary of
`Misc.nth_error_map_iff` immediately after destructing `nth_error l i`.  This
removes the separate mapped-`None` proof and the `length > i` detour while
preserving the statement and path.  This is the best local prototype in the
file because `transpose_spec` is its only internal caller.

## `transpose_spec` (`818`; proof `823-878`, 56 proof lines)

**Purpose.** Establishes the representation theorem for rectangular
transpose: `ij_error i j tapes = ij_error j i (transpose len tapes)`.

**Why it is long.** The empty matrix must distinguish whether a requested
column is within the explicit `repeat [] len` result (`824-852`).  The nonempty
case separates the first row/column (`853-861`) from recursive row and column
removal (`862-877`).

**Assessment.** This is a central, genuinely structural theorem.  Keep the
proof shape.  Add named comments for empty matrix, first-row lookup, and
recursive submatrix.  The duplicated empty-matrix subcases can use one local
lookup fact for `repeat [] len`, but extraction is optional and should be
measured for readability rather than line count.



---

# Long-proof audit: `lib/Linalg.v`

## `dot_product_aBp_assoc` (`1052`; proof `1057-1095`, 39 proof lines)

**Purpose.** Converts a dot product over columns of a transposed matrix into a
dot product over rows.  It is the algebraic bridge used by matrix-product
associativity.

**Why it is long.** The induction on matrix rows has a distinct empty-matrix
case (`1058-1064`), an empty-head-row normalization (`1069-1080`), and a
nonempty-head-row step using `dot_product_zip_with` (`1081-1094`).  Rectangular
width obligations account for the remaining proof.

**Assessment.** Substantive proof, correctly owned next to dot and matrix
products.  Add phase comments and name the rectangular-width hypotheses.  A
local empty-row normalization helper is possible but has no demonstrated reuse;
do not abstract it before measuring clarity.

## `matrix_product_assoc` (`1117`; proof `1121-1169`, 49 proof lines)

**Purpose.** Proves that the encoded affine matrix composition acts like
successive `affine_product` applications.

**Why it is long.** The induction first rewrites the tail (`1122-1131`), then
separates the empty right matrix (`1132-1138`).  The nonempty case decomposes
affine constants and vector products (`1139-1147`), reconstructs a column-width
fact by repeatedly unfolding `exact_listzzs_cols` (`1148-1158`), and invokes
`dot_product_aBp_assoc` (`1159-1166`).

**Low-risk refactor.** Add head/tail/member lemmas for `exact_listzzs_cols` at
its definition (`948-952`) and replace the two `map_fst_in`/unfold blocks.  Move
the generic `map_fst_in` implementation to `ListExt`, retaining a Linalg wrapper
if compatibility requires it.  Keep the theorem and its high-level induction.



---

# Long-proof audit: `lib/LinalgExt.v`

## `is_eq_iff_cmp_eq` (`18`; proof `21-97`, 77 proof lines)

**Purpose.** Connects the vector equality Boolean, which ignores trailing
zeroes, with `lex_compare = Eq`.

**Why it is long.** Both implication directions repeat the induction's
empty/nonempty and zero-padding cases.  The statement is heavily used and is
the equality case needed by transitivity.

**Low-risk refactor.** Prove named forward and backward lemmas, then assemble
the existing iff theorem.  This preserves the public theorem while giving
consumers directional APIs and clearer proof phases.

## `lex_compare_nil_trans` (`100`; proof `105-152`, 48 proof lines)

**Purpose.** Handles the special transitivity situation with an empty middle
vector and padded-zero lexicographic comparison.

**Why it is long.** It performs an exhaustive comparison-result, second-list,
and head-sign split (16 `destruct`s).  Three recursive cases are the only
substantive steps.

**Assessment.** Keep as a named internal bridge.  Add comments that separate
`Eq`, `Lt`, and `Gt`.  It is not externally referenced, but it is a direct
dependency of the public `lex_compare_trans` theorem.

## `lex_compare_trans` (`154`; proof `159-515`, 357 proof lines)

**Purpose.** Proves same-comparison transitivity for padded-zero
lexicographic vectors.

**Why it is long.** The proof contains 66 `destruct`s and separately expands
nearly mirror-image `Lt` and `Gt` case trees.  The `Eq` branch is conceptually
different and already uses `is_eq_iff_cmp_eq`; the strict branches repeatedly
perform the same head comparison and empty-tail reasoning.

**P0 refactor behind the unchanged theorem.** Prove a strict-`Lt`
transitivity theorem once.  Derive `Gt` by applying `lex_compare_antisym` to
both hypotheses and the conclusion.  Derive `Eq` by translating through
`is_eq_iff_cmp_eq` and the existing equality compatibility laws.  Then retain
`lex_compare_trans` as a three-case dispatcher.  This file is the correct owner:
`Linalg` defines `lex_compare` and already imports `ListExt`, so moving these
facts downward to `ListExt` would create a cycle.



---

# Long-proof audit: `polygen/InstanceListSema.v`

## `strongly_sorted_lists_by_timestamp_equal` (`248`; proof `256-328`, 73 proof lines)

**Purpose.** Shows equality of two strongly timestamp-sorted, timestamp-unique
instruction-point lists with the same ordinary membership.

**Why it is long.** After empty-list cases, lines `262-299` prove the heads are
equal.  If neither head is syntactically the other, sortedness yields both
timestamp directions, antisymmetry yields schedule equality, and `NoDupA`
turns that into a contradiction.  Lines `300-327` recurse on tails and again
use `NoDupA` to exclude the removed head.

**Assessment.** The argument is substantive but the current assertion names
are weak and the two tail-membership branches are symmetric.  If retained, add
phase comments and local names for head membership, cross-tail membership,
bidirectional order, and tail extensionality.  Do not extract a generic
`StronglySorted` theorem during the first canonicalization batch.

**Reachability.** No repository token caller was found for this theorem or the
three wrappers depending on it (`Sorted_incl_eq`,
`Sorted_same_ele_nodup_implies_sema_eq`, and its stable variant).  This is a
separate external-API/dead-route decision, not a reason to remove it while
adding the missing core semantic inversion API.
