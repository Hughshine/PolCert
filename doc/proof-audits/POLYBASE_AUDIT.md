# Read-only audit summary: `src/PolyBase.v`

## Scope and method

Audited the 2,513-line file on `proof/readability-cleanup`, together with the
relevant boundaries in `src/Base.v`, `lib/Linalg.v`, `lib/LinalgExt.v`,
`lib/Misc.v`, and `lib/ListExt.v`. The declaration inventory records source
span, proof span, internal dependencies/callers, external token uses, closure
from externally used declarations, tactic counts, semantic role, ownership, and
a proposed action.

Reachability is deliberately conservative and lexical:

- top-level names are searched as unqualified tokens outside `PolyBase.v`;
- nested `NP` names are searched qualified;
- same-named declarations elsewhere are treated as collisions, not callers;
- transitive dependencies of external roots are retained;
- implicit typeclass resolution is not visible to this analysis, so an exported
  `Instance` with no explicit name use is not classified as dead.

Artifacts:

- `/tmp/polybase_declarations.csv`: all declarations and dependency metadata.
- `/tmp/polybase_long_proofs.md`: individual review of every proof with at least
  30 proof lines.
- `/tmp/polybase_summary.md`: this summary.

## Inventory

- 108 source declarations: 52 lemmas, 38 definitions, 11 fixpoints, 3
  instances, 2 module aliases, 1 record, and 1 generated equality scheme.
- 56 proofs in total.
- 15 proofs have at least 30 proof lines; all 15 are in the live dependency
  closure of a repository consumer.
- 44 declarations have explicit external token uses.
- 98 of 108 declarations are either explicit roots or dependencies of roots.
- `PolyBase` is directly imported by 34 repository files, so path/API changes
  have broad compile impact even when a declaration has few direct uses.

The role distribution is: 20 zero-side lexicographic helpers, 15 structural
equality declarations, 12 general lexicographic declarations, 10 generic
vector/dot-product facts, 9 core polyhedral aliases, 8 memory-cell declarations,
8 schedule equality/nondecrease declarations, 8 product-space declarations, 7
legacy numbered-point-set declarations, 4 environment-equality declarations,
3 generic list facts, and 4 isolated declarations of other kinds.

## Reader path and current ownership

1. **Foundational representation (`20-321`).** Core aliases for domains,
   affine functions, schedules, accesses, points, memory cells, and timestamps;
   structural equality checkers and memory-cell relations. These are the public
   data-model surface and are widely consumed.
2. **Vector support (`323-425`).** Zero vectors, pointwise negation, and generic
   dot-product lemmas. These support later encodings but are not PolyBase-specific.
3. **Lexicographic polyhedra (`429-1612`).** Atomic strict/equality constraints,
   comparison against an implicit zero timestamp, and general first-difference
   constructions for `Lt` and `Gt`.
4. **Schedule equality and nondecrease (`1614-2029`).** All-zero tail
   constructions, general schedule equality, and the `Eq or Gt` construction.
5. **Product-space embedding (`2032-2244`).** Embeds two independent
   polyhedra into a concatenated point and proves their conjunction semantics.
6. **Environment-prefix equality (`2246-2513`).** Emits two constraints per
   shared environment coordinate and proves their sufficiency.

This order is semantically coherent, but the generic list/vector library facts
interrupt the PolyBase narrative and cause downstream files to duplicate them.

## Public and potentially unreachable declarations

The largest explicit external surfaces are `Schedule` (145 raw uses),
`AccessFunction` (100), `exact_cell` (58), `cell_neq` (50), and the structural
equality/polyhedron constructors used by validators. The central proof roots
include `make_poly_lt_correct`, `make_constr_gt_correct`,
`make_poly_eq_correct_true`, `make_poly_ge_correct`, `poly_product_correct`, and
`make_poly_env_eq_correct`.

Ten declarations are outside the explicit-root closure:

- `NP.t`, `NP.eq`, `NP.eq_refl`, `NP.eq_equiv`, `NP.eq_dec`, `NPSet`, and
  `NPSetProp`: a self-contained numbered-point weak-set block with no explicit
  repository consumer. Isolate or retire it only after checking external clients.
- `make_poly_eq_correct_false`: no repository caller; it is mechanically
  derivable from `make_poly_eq_correct_true` and Boolean discrimination. Retain
  a thin wrapper only for compatibility.
- `sequence_lesser`: self-recursive and has no caller. It is the strongest
  removal candidate.
- `cell_eq_proper`: no explicit named caller, but it is an exported `Instance`;
  typeclass use must be checked with compilation before any removal.

`list_beq` at `PolyBase.v:18` is not an external root: `Base.v:15` already runs
the identical `Scheme Equality for list`. PolyBase's internal equality checkers
can reuse the Base declaration.

## Library-boundary findings

### Move or canonicalize in Linalg

`V0`, `Vopp`, `opp_app`, `opp_opp`, `opp_v0_v0`,
`v0_n_app_1_dot_product_p_is_nth_p`,
`dot_product_v0_with_shorter_is_0`, `dot_product_opp_l`, and
`dot_product_opp_r` (`PolyBase.v:323-425`) are generic vector algebra. They
belong beside vector/dot-product definitions in `Linalg.v` or, if maintainers
want to avoid modifying the inherited core, in `LinalgExt.v`.

The repository already contains two equivalent right-negation proofs:
`ISSRefinement.v:183` (`dot_product_opp_right_local`) and `Extractor.v:751`
(`dot_product_opp_right`). A single canonical theorem would remove three proof
sites. Preserve existing names as wrappers where qualified paths matter.

`nth_assign_different` belongs beside `assign` and its laws at
`Linalg.v:1478-1536`. Its current 40-line implementation unfolds `assign` and
uses a classical ordering split; a pointwise `nth_assign` specification would
make the off-index corollary short and reusable.

`exact_listzzs_cols` is defined at `Linalg.v:948`, but users repeatedly unfold
it and solve head/tail/app preservation with `firstorder`. Add canonical:

- head row-width extraction;
- tail preservation;
- cons introduction/elimination;
- append preservation.

Independent local `exact_listzzs_cols_app` proofs in `PrepareCodegen.v:141` and
`StrengthenDomain.v:256`, plus a local component theorem in
`TilingBandScheduleValidator.v:4086`, confirm this is a missing Linalg API, not
a PolyBase-specific issue.

### Reuse or move generic list facts

- `nth_repeat_default` duplicates `Misc.nth_repeat` at `lib/Misc.v:109`.
- `firstn_eq_implies_nth_eq` and `firstn_ge_implies_firstn` are generic list
  consequences. `Misc.v` is the natural lowest layer; `ListExt.v` already
  imports `Misc.v`, so moving upward into ListExt would also be acyclic, but
  placing a helper in Misc maximizes reuse. The second result can be proved
  from `firstn_firstn` instead of by a fresh structural induction.
- Do not make `Misc.v` import `ListExt.v`: `ListExt.v` already imports Misc and
  that would create a cycle.

### Add one generic polyhedron-map lemma

`map_constr_transl_l_correct` and `map_constr_transl_r_correct` duplicate the
generic lifting of an atomic constraint equivalence through `map` and
`in_poly = forallb ...`. A parameterized `in_poly_map_iff` next to
`Linalg.v:401-413` can be proved using the existing `Misc.forallb_map`, then the
two PolyBase theorems remain domain-specific wrappers.

## Long-proof diagnosis

The 15 long proofs fall into five families:

- **Six lexicographic first-difference proofs:** four comparisons against an
  implicit zero timestamp plus general `Lt` and `Gt`. Their induction is
  substantive, but left/right and direction cases are strongly duplicated.
- **Four equality proofs:** atomic row equality, two all-zero schedule tails,
  and general schedule equality. The all-zero proofs rederive atomic facts that
  existing equality-row constructors already express.
- **Two product embedding proofs:** generic `map`/`forallb` lifting dominates.
- **Two environment proofs/helpers:** the main proof literally duplicates its
  two signed constraint branches; `nth_assign_different` is misplaced generic
  vector plumbing.
- **One atomic right-zero equality proof:** normalization-heavy mirror of the
  left theorem.

The detailed report gives theorem-by-theorem line ranges and extraction points.

## Minimal low-risk refactoring order

1. Remove the duplicate `Scheme Equality for list` command and reuse Base's
   declaration; compile all importers to confirm no qualified-path dependency.
2. Add generic list/Linalg lemmas and keep PolyBase-facing theorem wrappers.
   This has the best readability-to-risk ratio and reduces proof search noise.
3. Replace repeated `unfold exact_listzzs_cols; ... firstorder` fragments with
   named head/tail/app facts.
4. Add a local signed-coordinate helper for `make_poly_env_eq'_correct`; it
   removes the explicitly copied 39-line branch without changing the checker.
5. Reuse equality-row correctness in `make_poly_all0_l/r_correct`.
6. Add `in_poly_map_iff` and shorten the product-space proofs.
7. Add phase comments and semantic hypothesis names to the central `Lt`, `Gt`,
   and equality proofs.
8. Only after measuring compile time and proof clarity, prototype a shared
   comparison-direction induction for the six lexicographic proofs. This is the
   only proposed refactor with meaningful type-engineering/API risk.
9. Separately audit external API expectations before removing the `NP` block,
   `sequence_lesser`, or the unused negative equality theorem.

## Suggested measurable prototype

The safest prototype is not the largest abstraction. In an isolated worktree:

1. add `exact_listzzs_cols_head/tail/app`, a canonical `nth_assign`/off-index
   lemma, and `in_poly_map_iff` to Linalg;
2. retain all existing PolyBase names as wrappers;
3. refactor only `map_constr_transl_l/r_correct` and
   `make_poly_env_eq'_correct` first;
4. record clean `coqc` wall time for `Linalg.vo`, `PolyBase.vo`, and the direct
   validator importers before and after;
5. compare proof-line count and rebuild fanout, then decide whether the mirrored
   lexicographic induction is worth generalizing.

This prototype avoids changing executable definitions and keeps every current
public constructor, theorem name, and checker behavior visible.

---

# `src/PolyBase.v`: proofs with at least 30 proof lines

Line counts use the current `proof/readability-cleanup` source and count from
`Proof.` through `Qed.`. All fifteen proofs are in the dependency closure of an
explicit repository use; none is a candidate for deletion merely because it is
long.

## 1. Atomic equality against zero

### `make_constrs_eq0_r_correct` (`518-548`, 31 proof lines)

**Role.** Shows that two inequalities over the right component of `p1 ++ p2`
encode one affine expression being zero. It feeds both right-hand empty-schedule
lexicographic bridges.

**Why it is long.** The proof manually normalizes both constraints: `in_poly`,
`forallb`, appended zero vectors, vector negation, dot-product commutativity,
and Boolean inequalities. This is the right-hand mirror of the preceding
`make_constrs_eq0_l_correct` proof.

**Assessment.** The semantic fact is simple; most lines are normalization.
The minimum-risk improvement is a shared lemma saying that the two canonical
opposite inequalities are equivalent to equality. Preserve both public theorem
names as wrappers. If no helper is extracted, add stage comments before
`513-521` (decode the two rows), `523-533` (equality implies both rows), and
`535-546` (both rows imply equality).

## 2. Lexicographic comparison with an implicit zero schedule

These four proofs implement the same recursive argument. The list of candidate
polyhedra represents the first schedule coordinate at which the nonempty
timestamp differs from the implicit all-zero timestamp. The left variants also
carry repeated obligations from `exact_listzzs_cols`; the right variants only
need the length of the zero prefix.

### `make_poly_lt0_l_correct` (`566-666`, 101 proof lines)

**Structure.** Empty schedule contradiction (`567-577`); split on the affine
head value (`578-631`); reconstruct the semantic comparison from either the
head candidate or recursive candidates (`633-663`).

**Why it is long.** The proof repeatedly derives the head/tail consequences of
`exact_listzzs_cols` (`593-605`, `627-629`, `643-645`, `657-662`), manually
opens `Exists`, and reconstructs a nonempty tail timestamp after
`affine_product` was destructed.

**Refactor.** First add named head and tail lemmas for
`exact_listzzs_cols` in `Linalg.v`; this is a low-risk reduction in anonymous
`clear; firstorder` blocks. A later, medium-risk refactor can share one proof
schema with the other three zero-side comparisons while leaving all executable
constructors and theorem paths intact.

### `make_poly_lt0_r_correct` (`684-760`, 77 proof lines)

**Structure.** Empty contradiction (`685-695`); zero head recurses and adds
equality rows (`697-726`); strictly positive head selects the first candidate
(`728-736`); reverse direction distinguishes the head candidate from recursive
candidates (`738-757`).

**Assessment.** Substantive induction, but nearly all structure mirrors
`make_poly_lt0_l_correct`; it is shorter only because it has no row-width
invariant to peel. Share a direction/side proof schema only after the small
library facts have been extracted. In-place phase comments are otherwise enough.

### `make_poly_gt0_l_correct` (`825-919`, 95 proof lines)

**Structure.** Same three phases as `make_poly_lt0_l_correct`: base
(`826-836`), forward first-difference construction (`837-889`), and reverse
candidate interpretation (`891-916`).

**Assessment.** This is the greater-than mirror of `make_poly_lt0_l_correct`.
Its repeated `exact_listzzs_cols` projections (`851-863`, `885-887`,
`899-911`) should use the same named library lemmas. Preserve the public theorem
as a thin direction-specific wrapper if a generic comparison proof is added.

### `make_poly_gt0_r_correct` (`938-1015`, 78 proof lines)

**Structure.** Base (`939-949`), forward equality/strict-head split
(`950-990`), and reverse head/recursive candidate split (`992-1012`).

**Assessment.** Same semantic induction as `make_poly_lt0_r_correct`, with the
opposite atomic constraint. A shared proof schema is justified by the four-way
duplication, but is not a prerequisite for readability: accurate phase comments
and names for the candidate cases would already make the existing proof legible.
The commented obsolete implementation after `Qed.` (`1016-1027`) should be
removed or moved to history; it currently inflates the apparent declaration.

## 3. Equality of affine schedule rows

### `make_constrs_eq_correct` (`1062-1107`, 46 proof lines)

**Role.** Interprets two opposite inequalities as equality between two affine
row values. It is reused by less-than, greater-than, and schedule equality.

**Why it is long.** Both directions independently normalize appended and
negated vectors, commute dot products, then turn two `Z.leb` facts into an
equality. The proof has two anonymous assertions (`1071-1088`) whose meanings
are the two directions of the order.

**Refactor.** A canonical Linalg lemma for dot products under `map Z.opp`, plus
a local helper for the two-inequalities/equality equivalence, would leave this
proof as the single polyhedral instantiation. At minimum name the assertions
`Hle12` and `Hle21` and add comments before `1063`, `1071`, and `1091`.

## 4. General lexicographic comparison

### `make_poly_lt_correct'` (`1143-1312`, 170 proof lines)

**Role.** Central representation theorem for `make_poly_lt`: a semantic
lexicographic `Lt`, under an accumulated polyhedron, iff one generated
first-difference polyhedron accepts the paired point.

**Structure.** Empty left schedule, including the nonempty-right bridge
(`1144-1191`); nonempty left versus empty right (`1193-1206`); both nonempty,
forward head comparison (`1207-1256`); both nonempty, reverse interpretation of
head versus recursive candidate (`1258-1309`).

**Why it is long.** The semantic case split is inherently central, but the proof
also repeats row-width extraction (`1221-1234`, `1241-1244`, `1282-1285`,
`1298-1307`), manually shuffles singleton/appended polyhedra, and mirrors most
of `make_poly_gt_correct'`.

**Refactor.** Low risk: introduce `exact_listzzs_cols_head` and
`exact_listzzs_cols_tail`, and name the two directions and the head comparison
cases. Medium risk: factor the first-difference induction over a comparison
direction, preserving `make_poly_lt`, `make_poly_lt_correct'`, and
`make_poly_lt_correct` as the visible API. This proof should not be hidden behind
automation; its four semantic phases deserve explicit comments.

### `make_poly_gt_correct'` (`1434-1590`, 157 proof lines)

**Role.** Greater-than counterpart of the preceding theorem.

**Structure.** Empty-left bridge (`1435-1476`); nonempty-left/empty-right
bridge (`1478-1488`); forward equality, impossible, and strict cases
(`1489-1538`); reverse head/recursive candidate cases (`1540-1587`).

**Why it is long.** It is a near structural mirror of the `Lt` proof and repeats
the same row-width derivations and singleton-polyhedron plumbing.

**Refactor.** Use the same two-stage plan as for `make_poly_lt_correct'`.
The comment at `1420-1421` says “Only soundness”, but this theorem states an
`iff`; the one-way wrapper is `make_poly_gt_correct` at `1593`. Correcting that
comment is a documentation fix, not a proof change.

## 5. Equality of complete schedules

### `make_poly_all0_l_correct` (`1649-1747`, 99 proof lines)

**Role.** When only the left schedule has rows, shows that the emitted row pairs
are satisfied exactly when every left timestamp component is zero.

**Why it is long.** For every recursive head, both directions separately
re-prove that the two emitted inequalities force `a*p+c = 0` (`1664-1699`) and
that equality satisfies both inequalities (`1711-1740`). These are the same
atomic facts already represented by `make_constrs_eq0_l`.

**Refactor.** Define the constructor in terms of the existing equality-row
constructor, or prove a small equivalence between its two head rows and
`make_constrs_eq0_l`; then the proof becomes induction plus the atomic theorem.
Preserve `make_poly_all0_l` and this theorem as wrappers. Add comments at the
forward head equality, recursive tail, reverse head rows, and recursive tail if
the representation is left unchanged.

### `make_poly_all0_r_correct` (`1768-1864`, 97 proof lines)

**Role and structure.** Exact right-hand mirror of the preceding theorem:
forward extraction of zero head (`1777-1818`) and reverse construction of the
two head rows plus recursion (`1820-1861`).

**Refactor.** Reuse `make_constrs_eq0_r_correct`, or a shared canonical
two-inequality equality lemma. The 97 lines are normalization duplication, not
new semantic complexity.

### `make_poly_eq_correct_true` (`1896-1952`, 57 proof lines)

**Role.** Central theorem for schedule equality, covering equal-length heads and
the two unequal-length/all-zero tails.

**Why it is long.** Its case structure is legitimate. Remaining noise comes
from repeatedly peeling `exact_listzzs_cols` (`1927-1932`, `1943-1948`) and
low-information hypothesis names after inversion.

**Refactor.** Once the all-zero bridges and row-width lemmas are simplified,
this proof is close to an appropriate final shape. Prefer phase comments and
semantic hypothesis names over another abstraction. The unused
`make_poly_eq_correct_false` (`1954-1977`) can be a short Boolean corollary of
this theorem if retained for compatibility.

## 6. Product-space embeddings

### `map_constr_transl_l_correct` (`2074-2126`, 53 proof lines)

**Role.** Lifts atomic left-embedding correctness across a polyhedron represented
by `forallb`.

**Why it is long.** Both directions repeat the same list induction, Boolean
conjunction decomposition, atomic theorem application, and extraction of the
head row width from `exact_listzzs_cols` (`2083-2102`, `2105-2123`).

**Refactor.** Add a generic `in_poly_map_iff`/`forallb_map_iff` preservation
lemma beside `in_poly` in `Linalg.v`, parameterized by the atomic constraint
equivalence. Then this theorem is one application plus the row-width premise.
This helper is useful outside PolyBase and does not encode polyhedral scheduling.

### `map_constr_transl_r_correct` (`2172-2203`, 32 proof lines)

**Role.** Right-embedding counterpart.

**Why it is long.** Same generic `map`/`forallb` lifting as the left theorem,
without the per-row width premise.

**Refactor.** Use the same `in_poly_map_iff` helper. The proof can then remain a
small public wrapper around `constr_transl_r_correct`.

## 7. Environment-prefix equality

### `nth_assign_different` (`2282-2321`, 40 proof lines)

**Role.** Updating one vector coordinate leaves every distinct in-bounds
coordinate unchanged. It is used only by `make_poly_env_eq'_correct` here.

**Why it is long.** It unfolds the list-splicing implementation of `assign`,
performs nine destruct/case splits, invokes classical order comparison, and
manually reasons through `resize`, append, and `skipn`.

**Assessment and ownership.** This is a generic fact about `assign`, whose
definition and existing laws live at `lib/Linalg.v:1478-1536`. Move a canonical
off-index theorem there (ideally derive it from one pointwise `nth_assign`
specification), and retain a compatibility wrapper in PolyBase only if the path
must remain visible. The use of `Classical` is an implementation artifact, not
intrinsic to the theorem.

### `make_poly_env_eq'_correct` (`2385-2494`, 110 proof lines)

**Role.** For each of the first `n` environment coordinates, emits the two
opposite inequalities that require the coordinate in `p1` to equal the
corresponding coordinate in `p2`; proves the construction sufficient for
`in_poly`.

**Structure.** Empty prefix (`2386-2389`); expose nonempty point and environment
dimensions (`2390-2401`); prove the `-x+y <= 0` row (`2402-2441`); prove the
opposite row (`2442-2480`); recurse on the shorter prefix (`2481-2492`).

**Why it is long.** The two row proofs are almost literal copies; the source
marks the second `(* copy paste *)`. Each repeats the same app-index equality,
zero-vector lookup, off-index assignment fact, and dot-product normalization.

**Refactor.** Extract a local signed-coordinate constraint lemma immediately
before this theorem: given equality of the two selected coordinates, prove the
constraint formed by assigning coefficients `s` and `-s` for `s = 1` or
`s = -1`. Alternatively, extract the common coordinate-index equality
(`2413-2426` / `2452-2465`) and one atomic row evaluator. This removes the
largest accidental duplication without changing the constructor, theorem, or
module paths. The recursive phase should remain explicit. Generic helpers
`nth_repeat_default`, `firstn_eq_implies_nth_eq`, and
`firstn_ge_implies_firstn` belong in the list library; the first already overlaps
`Misc.nth_repeat`, and the last can be expressed using `firstn_firstn`.

## Priority order

1. Add/reuse generic Linalg and list facts while preserving PolyBase wrappers.
2. Replace anonymous `exact_listzzs_cols` derivations with named head/tail lemmas.
3. Extract the common signed environment-row helper.
4. Reuse atomic equality constructors in the all-zero schedule proofs.
5. Add a generic `in_poly`-over-`map` lifting lemma.
6. Only then consider a shared comparison-direction proof schema for the six
   lexicographic proofs. That abstraction has the highest type-engineering risk
   and should be justified by measured compile/readability improvement.
