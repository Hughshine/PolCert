# Read-only audit summary: `src/TilingBoolChecker.v`

## Inventory and method

Audited all 515 lines and all declarations in the `TilingBoolChecker (Instr:
INSTR)` functor. `/tmp/tiling_bool_checker_declarations.csv` records declaration
and proof spans, internal dependencies/callers, qualified uses outside the file,
the transitive external-root closure, ownership, and recommended action.

- 25 declarations: 3 module aliases, 9 definitions, 2 fixpoints, and 11 lemmas.
- 11 proofs; only 2 have at least 30 proof lines.
- 7 members have qualified external uses.
- 19 declarations are in the active external-root closure.
- The six declarations outside that closure are exactly the compiled-form
  checker chain.

External reachability counts only qualified member selection from an instantiated
functor (`TilingCheck.foo`, including longer prefixes such as
`Core.TilingCheck.foo`). This avoids confusing the functor's short `Tiling`,
`PL`, and `Ty` aliases with unrelated modules. It is still a repository-local,
lexical analysis; intended clients outside the repository may rely on exported
members.

Artifacts:

- `/tmp/tiling_bool_checker_declarations.csv`
- `/tmp/tiling_bool_checker_long_proofs.md`
- `/tmp/tiling_bool_checker_summary.md`

## What this checker actually certifies

The active entry point is `check_pprog_tiling_sourceb`. A successful check is
decoded by `check_pprog_tiling_sourceb_sound` into five groups of facts:

1. the declarative source-form structural relation from `TilingRelation`;
2. every source statement starts with the identity point-space witness;
3. every statement tiling witness is dimensionally well formed;
4. every tile size is positive;
5. every witness point dimension equals its source statement depth.

At statement level, the structural checker tests:

- unchanged instruction;
- target depth equals source depth plus the number of tile links;
- target point witness is the compiled tiling witness;
- source-form transformation and access-transformation fields remain unchanged;
- the target domain is exactly the compiled link domain followed by the lifted
  source domain;
- source-form read and write access descriptions remain unchanged.

At program level, it additionally checks that statement lists and witnesses
have matching shape, and that identifier and typed-variable contexts are equal.

These are exact representation checks, not a dependence or schedule legality
test. The file contains no comparison of `pi_schedule` at all.

## Boundary with `TilingRelation`

`TilingRelation.v` owns the declarative objects and their semantics:

- witness well-formedness (`well_formed_tile_links` and
  `wf_statement_tiling_witness_with_param_dim`);
- compilation of tile-link interval constraints;
- lifting of domains, transformations, and accesses;
- statement/list/program structural relations;
- the semantic domain, index, access, timestamp, and state-equivalence theorems.

`TilingBoolChecker.v` should own only executable reflection of the finite,
syntactic premises into those propositions. Its soundness theorems are the
boundary: they turn `bool = true` into `TilingRelation` hypotheses. The current
dependency direction is appropriate: BoolChecker imports Relation; Relation
does not import the checker.

The witness checker mirrors `TilingWitness.well_formed_tile_links`: link `k`
must have `k + point_dim` variable coefficients, every parameter row must have
`param_dim` coefficients, and each tile size must be positive. Positivity is
returned separately because it is a semantic precondition for division and
tile-interval results, not part of the current `well_formed_tile_links`
definition.

## Boundary with canonical and permutable-band validation

`TilingBoolChecker` establishes that the submitted target has the expected
tiled representation. It does **not** establish that the new execution order is
legal.

The downstream split is deliberate:

- `TilingCanonicalScheduleValidator` separately checks a canonical lifted
  schedule shape.
- `TilingBandScheduleValidator` reuses the source structural gate, infers/checks
  tiling bands and schedule layouts, and supplies the permutability/reordering
  premise. For example, its correctness theorems accept
  `check_pprog_tiling_sourceb = true` as the structural hypothesis and a
  separate `pprog_permutable_tiling_bands` or
  `pprog_tiling_reordering_safe` hypothesis.
- Phase-scalar, mixed second-level, and direct-runtime routes all reuse the same
  source structural check before their specialized band reasoning.

Thus the correct reader pipeline is:

`boolean structure check` -> `TilingRelation structural facts` ->
`schedule-layout/band check` -> `permutability or reordering theorem` ->
`semantic equivalence`.

Merging band legality into this file would blur a useful boundary and make the
basic representation checker harder to reuse across ordinary, diamond,
second-level, and mixed routes.

## Declaration groups

### Shared context equality (`20-72`)

`ctxt_eqb`, `ctxt_ty_eqb`, and their soundness lemmas are not tiling-specific.
Equivalent implementations occur in `AffineValidator.v:348-409` and
`ISSBoolChecker.v:28-74`. The `INSTR` and `TY` interfaces already provide iff
specifications for element equality, so a shared Instr-parameterized checker
utility can expose:

- Boolean equality for identifier contexts;
- Boolean equality for typed contexts;
- one iff theorem and reflexivity theorem for each.

Retain the current functor member names as aliases/wrappers so all band modules
keep their public paths. `ctxt_ty_eqb_eq` is currently implication-only even
though an iff is provable; add a new shared spec rather than silently changing
its public theorem type.

### Witness shape (`74-164`)

The definitions and their soundness chain are cohesive and correctly owned.
`forallb_link_params_positive_sound` is the only generic-looking piece: its list
traversal can use a standard/local `forallb`-to-`Forall` reflection helper while
the atomic parameter-length/positivity fact remains here. At 15 proof lines,
generalization is optional.

### One statement (`166-315`)

The source and compiled definitions mirror two declarative representations.
Their soundness proofs are field-by-field conjunction decoders. The explicit
field mapping is valuable; phase comments are preferable to a broad tactic that
hides the contract.

The source chain is active. The compiled chain is not selected by any qualified
repository consumer. This does not mean the declarative compiled relation is
dead: `TilingRelation` uses it extensively. Only this alternate **Boolean
checker** path is inactive.

### Lists and programs (`317-513`)

The list checkers synchronize three lists and recursively lift statement
soundness into the structural relation plus `Forall`/`Forall2` side conditions.
The program checkers add context equality. These proofs are short, direct, and
appropriately separated from statement checking.

## Long proofs and duplication

The only long proofs are:

- `check_pinstr_tiling_compiledb_sound` (`236-269`, 34 proof lines);
- `check_pinstr_tiling_sourceb_sound` (`280-315`, 36 proof lines).

Both are long because the public contract has ten or eleven Boolean clauses.
Neither contains difficult reasoning. The detailed report recommends phase
comments and semantic grouping, but not an opaque automation layer.

The compiled/source list and program soundness proofs are also mirrored but are
only 21-25 lines each. A higher-order synchronized-list checker abstraction
would cost more reader effort than it saves unless the pattern appears in
several additional validators.

## Reachability and dead-route candidates

Explicit roots are:

- module alias `Tiling` (selected once by `TilingValidator`);
- `ctxt_eqb`, `ctxt_eqb_eq`, `ctxt_ty_eqb`, `ctxt_ty_eqb_eq`;
- `check_pprog_tiling_sourceb` (57 qualified uses);
- `check_pprog_tiling_sourceb_sound` (27 qualified uses).

Everything in the source-form and witness-checking chain is reachable from
these roots. The following compiled-form chain is outside the repository-local
closure:

- `check_pinstr_tiling_compiledb`
- `check_pinstr_tiling_compiledb_sound`
- `check_pinstr_list_tiling_compiledb`
- `check_pinstr_list_tiling_compiledb_sound`
- `check_pprog_tiling_compiledb`
- `check_pprog_tiling_compiledb_sound`

Do not delete it as part of a readability pass without deciding whether the
compiled-form representation is an intended external compatibility API. A safe
first step is a section comment labeling it alternate/inactive in the current
pipeline.

## Low-risk refactoring order

1. Add a file-level proof map stating the structure/spec/schedule boundary and
   identify `check_pprog_tiling_sourceb` as the active structural gate.
2. Add phase comments to the two statement soundness proofs and align their
   hypothesis naming.
3. Centralize identifier and typed-context equality checkers in a shared
   Instr-parameterized utility, retaining aliases under every current module
   path.
4. Label the compiled-form checker chain as an alternate compatibility path;
   remove it only after an explicit API decision.
5. Optionally factor a small `forallb`/`Forall` reflection helper if another
   checker can reuse it.
6. Remove unused direct imports only after compile verification. `Lia` has no
   tactic use in this file, and `PolyLang` has no direct qualified reference;
   both appear redundant under the current dependency graph.

No checker definition, theorem, module path, or repository file was modified by
this audit.

---

# `src/TilingBoolChecker.v`: proofs with at least 30 proof lines

Only two proofs cross the 30-line threshold. Both are field-by-field reflection
proofs for one statement; neither contains the semantic tiling argument or the
permutable-band argument.

## `check_pinstr_tiling_compiledb_sound` (`236-269`, 34 proof lines)

**Statement.** A successful compiled-form statement check establishes
`Tiling.tiling_rel_pinstr_structure_compiled`, witness well-formedness at the
given parameter dimension, positivity of every tile size, and agreement between
the witness point dimension and the source statement depth.

**Proof phases.**

1. Bind the compiled witness and flatten the ten Boolean conjuncts (`237-249`).
2. Invoke statement-witness soundness once (`250-251`).
3. Convert each Boolean equality into the corresponding field equality of
   `tiling_rel_pinstr_structure_compiled` (`252-263`).
4. Return the three side conditions (`264-268`).

**Why it is long.** The checker is a ten-way right-associated `&&`; the proof
spends thirteen lines peeling it and eight lines applying existing equality
reflection lemmas. There is no difficult induction or arithmetic.

**Readability judgment.** Keep the explicit field-by-field conversion. A tactic
that blindly explodes all conjunctions would shorten the source while hiding
the correspondence between checker clauses and relation fields. Low-risk edits
would add the four phase comments above and rename the rolling `Hcheck` prefix
to `Hprefix` or use one destruct pattern with named leaves. A shared helper with
the source-form proof is possible but not compelling unless the compiled branch
remains public: the two relations deliberately differ in transformation/access
fields.

**Reachability.** No qualified repository consumer was found for this theorem
or any compiled-form checker. It remains relevant only as an intended external
API or alternate representation path.

## `check_pinstr_tiling_sourceb_sound` (`280-315`, 36 proof lines)

**Statement.** A successful source-form statement check establishes
`Tiling.tiling_rel_pinstr_structure_source`, identity of the source point-space
witness, witness well-formedness, positive tile sizes, and point-depth agreement.

**Proof phases.**

1. Bind the compiled witness and flatten the eleven Boolean conjuncts
   (`281-294`).
2. Invoke statement-witness soundness (`295-296`).
3. Convert the target statement fields into the declarative source structural
   relation (`297-307`).
4. Return the source identity condition and witness side conditions (`308-314`).

**Why it is long.** Like the compiled theorem, this is mechanical conjunction
decoding. It has one additional checked clause: the before statement must carry
`PSWIdentity (pi_depth before)`. The proof's length is proportional to the
public checker/spec contract, not to semantic complexity.

**Readability judgment.** This theorem is the central active boundary and
should remain explicit. Add phase comments, and place short comments beside the
three groups of clauses: statement identity/depth/witness, representation
fields, and domain/access fields. Do not extract it into an opaque generic
record-reflection tactic. If a helper is desired, the only low-risk candidate is
a local lemma that converts the five strict-equality booleans to equalities;
however, it saves little and obscures which representation is source-form.

**Reachability.** This theorem is an explicit root with 27 qualified uses. It is
consumed by `TilingValidator`, canonical schedule checking, phase-scalar/mixed
variants, the direct runtime, and many permutable-band routes.

## Near-threshold mirrored proofs

The four lifting proofs below are under 30 lines but account for most remaining
duplication:

- `check_pinstr_list_tiling_compiledb_sound` (`349-369`, 21 lines)
- `check_pinstr_list_tiling_sourceb_sound` (`383-405`, 23 lines)
- `check_pprog_tiling_compiledb_sound` (`444-468`, 25 lines)
- `check_pprog_tiling_sourceb_sound` (`489-513`, 25 lines)

The list pair recursively lifts one-statement soundness while accumulating
`Forall`/`Forall2` side conditions. The program pair decodes context equality
and invokes the list theorem. The proofs are already direct. A generic
three-list checker/soundness combinator would be reusable in principle, but it
would introduce a higher-order abstraction for roughly forty active lines.
Prefer symmetric phase comments and aligned naming unless further checkers show
the same pattern.
