# TilingValidator read-only audit summary

## Inventory

- Source: `src/TilingValidator.v`, 1,233 lines.
- Snapshot: commit `91621785168a74394f2b9c771bdd8427acc618b7`.
- SHA-256: `b59b0c1ed683a719fbd15c84dce1d1e8ade8f221cbfa84cc6919c305f2621258`.
- 74 declarations, including 17 nested `POLIRS` adapter definitions.
- 38 proof bodies, 731 inclusive proof-span lines, 655 nonblank proof-body lines.
- Five proofs are >=30 lines; they contain 50.2% of proof spans and 54.5% of nonblank proof lines.
- 16 declarations have direct qualified uses outside this file. Their lexical dependency closure reaches 52/74 declarations.
- Of the 22 outside that closure, 17 are required `POLIRS` adapter fields, four are compatibility/public naming aliases, and one is the substantive but repository-unreachable 106-line `outer_to_tiling_flatten_instr_nth_iff`.

Generated files:

- `/tmp/tiling-validator-proof-inventory.csv`: every declaration, exact lines/proof spans, internal callers/callees, qualified external uses, and reachability.
- `/tmp/tiling-validator-declaration-audit.csv`: the inventory plus responsibility, complexity, issue, priority, risk, and API constraint for all 74 declarations.
- `/tmp/tiling-validator-long-proofs.md`: complete review of all five >=30-line proofs.

## Responsibility boundary

This file has four roles:

1. Instantiate `AffineValidator` and `PrepareCodegen` over the internal tiling `PolyLang` by providing an inert `POLIRS` adapter.
2. Bridge records, flattening, and semantics between `PolIRs.PolyLang` and the separately instantiated `Tiling.PL`.
3. Implement the legacy/general checked tiling validator: structural witness checking plus affine validation of `retiled_old` against `after`, followed by `TilingRelation`'s proof from `retiled_old` back to `before`.
4. Compose successful validation with prepared code generation.

It is not the direct permutable-band checker. The newer direct-band modules use this file's representation/well-formedness/semantics bridge, while their tiling-specific proof lives in `TilingBandScheduleValidator` and related modules.

## Soundness finding

No checker-to-theorem disconnection was found here. The central `tiling_validate_correct` explicitly consumes:

- the structural tiling relation and witness conditions;
- `GeneralValidator.validate_tiling_correct` for `retiled_old -> after` reordering;
- `Tiling.tiling_retiled_old_to_before_instance_correct_source` for the tiling realization back to `before`;
- transitivity of state equivalence.

The checked wrapper obtains those premises from `check_pprog_tiling_sourceb_sound`, and the outer wrapper transports the resulting semantics back to `PolIRs.PolyLang`. The main issue is proof organization, not a missing semantic edge.

## P0 readability work

### 1. Package the outer/internal representation isomorphism

Four long proofs and most of the point/list bridge exist because two field-identical record families are copied manually. Add private pointwise inverse/injectivity lemmas and generic transports for membership, NoDup, Sorted, permutation, and instruction-list semantics. Keep every current exported theorem as a wrapper.

This addresses the largest proof-volume concentration without changing the public API or tiling theory.

### 2. Consolidate both flattening proofs

`outer_to_tiling_flatten_instr_nth_iff` is 106 proof lines with no repository caller. `outer_to_tiling_flatten_instrs_iff` is 113 proof lines on the live path and repeats almost the same two-direction map argument. Derive both from one private flatten-member transport over the representation isomorphism.

### 3. Name schedule-sorted transport

`outer_to_tiling_poly_instance_list_semantics_iff` reproves `Sorted instr_point_sched_le` transport inline in both directions. Add the exact named helper, then make the semantic theorem a composition of flatten, permutation, sorting, and instruction-semantics transports.

### 4. Simplify checked premise assembly

In `tiling_checked_validate_correct`, preserve `Hprog` and use existing `Tiling.tiling_rel_pprog_structure_source_lengths` rather than unfolding to the list relation and reconstructing `Hprog_full`. This is the lowest-risk immediate cleanup.

## P1 work

- Replace generic local `nth_error_map_inv`/`nth_error_map` implementations with qualified Rocq/ListExt facts or shared wrappers.
- Normalize use of `tiling_to_outer_ipl` instead of alternating between the alias and raw `List.map tiling_to_outer_ip`.
- Add an `AffineValidator` theorem that successful `validate_general` establishes well-formedness of the second program; use it to remove bind/boolean-shape dependence from `checked_tiling_validate_implies_wf_after`.
- Retain `TilingPolIRs` stubs for now. Removing them requires narrowing shared functor signatures and is a broader, high-risk architecture change.

## Recommended order

1. Low-risk checked-wrapper cleanup using the existing program-length lemma.
2. Introduce point/program representation inverse helpers and schedule-Sorted transport.
3. Rewrite the four long representation-semantic proofs as wrappers over those helpers.
4. Move generic list and validator-wf facts to their natural utility/validator owners.
5. Only then consider narrowing the `POLIRS` functor dependency.

No repository file was modified and no build was run.


---

# TilingValidator long-proof audit

## Scope and counting

- Source: `src/TilingValidator.v`, 1,233 lines.
- Snapshot: commit `91621785168a74394f2b9c771bdd8427acc618b7`.
- SHA-256: `b59b0c1ed683a719fbd15c84dce1d1e8ade8f221cbfa84cc6919c305f2621258`.
- Declarations: 74, including 17 definitions required by the nested `TilingPolIRs <: POLIRS` adapter.
- Proof bodies: 38; 731 inclusive `Proof.`-to-terminator lines and 655 nonblank body lines.
- Threshold: inclusive `Proof.` through `Qed.`/`Defined.` span >= 30 lines.
- Five proofs meet the threshold. They occupy 367/731 proof-span lines (50.2%) and 357/655 nonblank body lines (54.5%).

## What the long proofs are actually about

Four of the five long proofs do not establish tiling mathematics. `TilingBoolChecker Instr` and `PolIRs.PolyLang` contain separately instantiated `PolyLang` record types. The file manually copies records between them and proves that flattening and semantics survive the copy. The difficult tiling theorem is already supplied by `TilingRelation`; the local core theorem composes it with affine validation in only 23 nonblank proof lines.

## 1. `outer_to_tiling_flatten_instr_nth_iff`

- Declaration: lines 509-619.
- Proof: lines 514-619, 106 inclusive lines, 104 nonblank body lines.
- Repository reachability: no caller inside or outside this file.
- Risk: low-to-medium rewrite risk; preserve its exported name/type.

### Responsibility

It proves that `flatten_instr_nth` is invariant under copying one outer `PolyInstr` and an instruction-point list into the internal tiling `PolyLang` instance.

Each direction transports four parts of the flattening relation:

1. every point has the expected environment prefix;
2. list membership is equivalent to the point's prefix, `belongs_to`, statement number, and index length;
3. `NoDup`;
4. `Sorted np_lt`.

### Why it is long

The proof expands both directions independently. It repeatedly converts `In` through `in_map_iff`, reconstructs an entire six-field `InstrPoint` record for the inverse direction, destructs two records to prove injectivity, and then invokes separately directional NoDup/Sorted lemmas.

The length is representation plumbing, not theoretical complexity. The next theorem repeats nearly the same proof for a program list, so this 106-line theorem is currently both unused and duplicated.

### Refactor

P0, low-to-medium risk:

1. Add pointwise inverse lemmas for `outer_to_tiling_ip` and `tiling_to_outer_ip`.
2. Package injectivity, membership transport, `belongs_to`, `np_lt`, and point semantics as one private representation-isomorphism interface.
3. Prove a generic flatten transport lemma over that interface.
4. Retain this theorem as a short specialization, even though it has no repository caller.

Do not delete it without an API decision; it is exported from the functor even though repository-unreachable.

## 2. `outer_to_tiling_flatten_instrs_iff`

- Declaration: lines 621-738.
- Proof: lines 626-738, 113 inclusive lines, 111 nonblank body lines.
- Public path: `outer_to_tiling_poly_instance_list_semantics_iff` -> top-level semantics bridge -> checked outer validator/direct-band clients.
- Risk: medium because it is on the live semantic path.

### Responsibility

This is the program-list analogue of the previous theorem. In addition to instruction-point conversion, it transports the existential statement selected by `nth_error` in the flattened-program membership condition.

### Why it is long

It duplicates both directions of the 509-line theorem and adds manual `nth_error (map f xs)` inversion/construction. The inverse branch again spells out a complete record literal twice. No branch contains tiling arithmetic, schedule reasoning, or state semantics.

### Existing reusable facts

- The local `nth_error_map_inv` and `nth_error_map` are generic list facts duplicated in several project files. The pinned Rocq environment already exposes `nth_error_map_iff` in other modules.
- `outer_to_tiling_belongs_to_iff`, list inverse, NoDup, and Sorted bridges already exist locally but are unbundled.

### Refactor

P0, medium risk:

1. Use one named point/list isomorphism and one membership-transport lemma.
2. Use the existing `nth_error_map_iff` rather than two local recursive list proofs, retaining the public local names as wrappers if compatibility matters.
3. Share the flatten-member transport with `outer_to_tiling_flatten_instr_nth_iff` instead of keeping two independent 100-line proofs.
4. Keep the theorem statement unchanged because it is the foundation of the live semantics bridge.

## 3. `outer_to_tiling_poly_instance_list_semantics_iff`

- Declaration: lines 740-815.
- Proof: lines 745-815, 71 inclusive lines, 69 nonblank body lines.
- Public path: used by `outer_to_tiling_instance_list_semantics_iff`, which is used by the outer checked validator, canonical validator, and direct-band runtime.
- Risk: medium.

### Responsibility

It transports one fixed-environment polyhedral execution. After inverting `PolyPointListSema`, it reconstructs the corresponding constructor on the other `PolyLang` instance and transports:

1. flattened instruction points;
2. the permutation from the flattened list to execution order;
3. `Sorted instr_point_sched_le`;
4. instruction-point-list semantics.

### Why it is long

Both directions are written separately. More importantly, each direction contains a fresh induction transporting `Sorted instr_point_sched_le` even though the file already has pointwise schedule-order iff lemmas. The existing named `Sorted_*` lemmas cover `np_lt`, not `instr_point_sched_le`, so the exact reusable helper is missing.

### Refactor

P0, medium risk:

1. Add `Sorted_instr_point_sched_le` transport in both directions, derived from the pointwise iff and the representation inverse.
2. Add a small permutation transport iff for the inverse maps.
3. Reconstruct `PolyPointListSema` through one private generic direction lemma; obtain the reverse direction by instantiating the inverse isomorphism.
4. Keep this public iff as the visible proof boundary.

This should make the proof read as four named transports rather than two constructor-sized scripts.

## 4. `outer_to_tiling_instance_list_semantics_iff`

- Declaration: lines 817-859.
- Proof: lines 821-859, 39 inclusive lines, 37 nonblank body lines.
- Direct external uses: canonical schedule validation and direct-band runtime; also used by the local outer checked validator.
- Risk: low.

### Responsibility

It lifts the fixed-environment bridge through the top-level semantics constructor, preserving compatibility, non-aliasing, initial environment, and the transported poly-instance semantics.

### Why it is long

The two branches are symmetric and explicitly repeat every constructor argument (`pprog`, `pis`, `varctxt`, `vars`, `envv`). The only nontrivial step in either branch is the preceding poly-instance iff.

### Refactor

P0, low risk: add one private constructor-transport helper or use tightly controlled `econstructor` calls with named premises. Keep the two directions visible but reduce each to inversion, reconstruction, and one application of `outer_to_tiling_poly_instance_list_semantics_iff`.

## 5. `tiling_checked_validate_correct`

- Declaration: lines 1003-1056.
- Proof: lines 1019-1056, 38 inclusive lines, 36 nonblank body lines.
- Public path: `checked_tiling_validate_correct` -> `Validator` API -> driver tiling routes.
- Risk: low.

### Responsibility

It turns the executable structural checker result into the premises of `tiling_validate_correct`: structural source relation, identity precondition, witness well-formedness, positive tile sizes, point-depth agreement, and list lengths.

### Why it is long

After obtaining the full program relation `Hprog`, the proof unfolds and destructs it to substitute context/variable equality. It then drops to `tiling_rel_pinstr_list_source_lengths`, derives witness length manually, and reconstructs the same full program relation as `Hprog_full` over 12 lines.

### Existing lemma that should be used

`Tiling.tiling_rel_pprog_structure_source_lengths` (`src/TilingRelation.v:511-526`) already derives both program-list lengths from the full relation. Preserve a copy of `Hprog` before destructing context equalities, apply the program-level length lemma, and pass the preserved/re-written relation directly to `tiling_validate_correct`.

P0, low risk. This is the clearest immediate reduction because it removes duplicated proof assembly without changing theory or public contracts.

## Important sub-threshold findings

### `tiling_validate_correct` is the right core theorem

Lines 941-1001 expose many explicit premises, but the proof itself is concise and well layered:

1. `GeneralValidator.validate_tiling_correct` proves the validated `after` execution corresponds to `retiled_old`.
2. `Tiling.tiling_retiled_old_to_before_instance_correct_source` proves `retiled_old` corresponds to `before` under the structural tiling and witness premises.
3. State equivalence is composed transitively.

This theorem should remain explicit and readable. Compressing its premises or hiding the two semantic steps behind automation would reduce clarity.

### `checked_tiling_validate_implies_wf_after` is implementation-coupled

Lines 1135-1163 unfold `GeneralValidator.validate_general`/`validate_tiling`, destruct four monadic binds, repeatedly rewrite nested `andb`, and select the second well-formedness result from the boolean tuple. The argument is simple but brittle under validator implementation changes.

P1: add a theorem beside `AffineValidator.validate_general` saying a successful validation establishes `wf_pprog_general` for its second program. Then keep the current public theorem as a short consumer.

### Generic list helpers are duplicated

`nth_error_map_inv` and `nth_error_map` are not tiling-specific. Equivalent facts are already used from the Rocq list library elsewhere, and several project modules independently define another `nth_error_map_inv`. Prefer a shared/list-library fact and preserve these names only as wrappers if external compatibility is required.
