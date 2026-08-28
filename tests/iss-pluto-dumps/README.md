# Pluto ISS dump suite

This directory contains Pluto internal-program dumps used to test the
experimental ISS-only validator path.

These tests run in the base CI shard.

Current entry point:

```bash
opam exec -- make test-iss-pluto-suite
opam exec -- make test-iss-pluto-live-suite
```

That target builds `polopt` and runs:

```bash
./polopt --validate-iss-pluto-suite
./polopt --validate-iss-pluto-live-suite
```

The suite currently covers:

- positive Pluto ISS examples
  - `reverse_*`
  - `multi_stmt_periodic_*`
  - `jacobi_2d_periodic_*`
  - `heat_2dp_*`
- negative examples
  - fixed bad dump: `iss_name_collision.txt`
  - runtime-mutated bad halfspace
  - runtime-mutated bad payload
- adversarial complete-cut bridge examples
  - valid two-cut/four-piece sign partition
  - Pluto-style three-cut/four-piece metadata mismatch
  - two-cut partition with one sign region missing

Current proof/engineering boundary:

- the ISS validator does **not** use OpenScop
- the legacy dump suite validates Pluto debug dumps of the internal
  `PlutoProg / Stmt / Dep` representation
- the live suite validates Pluto's native `--dump-iss-bridge` export
- final accept/reject goes through the extracted Coq
  `complete-cut-shape` checker
- the Coq development now also contains the semantic theorem:
  `checked_iss_complete_cut_shape_validate = true`
  implies backward `PolyLang.instance_list_semantics`

What the current suite checks:

1. Legacy dump suite:
   Python bridge recovers each after-ISS family’s source statement payload
2. Legacy dump suite:
   Python bridge recovers source domains, cuts, and dependence remapping sanity
3. Live bridge suite:
   Pluto emits `before/after domains + cuts + stmt witnesses` directly
4. Coq checks each piece domain is `source_domain ++ selected_cut_constraints`
5. Coq checks each parent family’s `piece_signs` are non-duplicated
6. Coq checks each parent family covers the full expected `2^k` sign space

The multi-cut fixtures isolate item 6. `multicut_native_mismatch.bridge`
models the pinned Pluto `lib/iss.c` state in which three base cuts are recorded
but only four regions are constructed. `multicut_missing_piece.bridge` removes
one of the four regions for two cuts. Both must be rejected; the complete
two-cut partition must be accepted.

Current trusted-path status:

- Legacy dump path still includes Python witness recovery
  - payload/source recovery
  - dependence remapping explanation
- Native Pluto bridge path removes Python from the validation core
- Coq decides the final ISS structural check
  - `checked_iss_complete_cut_shape_validate`
- Coq proof-only modules provide the semantic correctness theorem
  - `ISSCutSemantics.v`
  - `ISSValidatorCorrect.v`
