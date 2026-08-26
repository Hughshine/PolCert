# Parallel annotation coordinate reproduction

> **Resolution on `artifact/verified-compilation-v9-candidate` (2026-08-07).** This document
> reproduces the pre-fix coordinate mismatch.  The validator certificate now
> denotes the canonical padded schedule coordinate used by code generation,
> and `RawCodegenOrigin` proves the source/generated coordinate relation used by
> checked single- and multi-coordinate correctness.

This is a read-only reproduction using the already-built `polopt` in container
`polcert-proof-readability`.  Repository files were not changed; container and
host outputs were written under `/tmp`.

## Commands

```sh
./polopt --diamond-tile --parallel-current 0 \
  tools/parallel_current/fixtures/jacobi-batch.loop

./polopt --diamond-tile --dump-scheduled-openscop \
  tools/parallel_current/fixtures/jacobi-batch.loop
```

Captured evidence:

- `/tmp/polcert-jacobi-raw-parallel.out`
- `/tmp/polcert-jacobi-raw-parallel.err`
- `/tmp/polcert-jacobi-scheduled-dump.out`

## Facts established

1. The requested certificate dimension is `d = 0`.  This is not inferred from
   output: `parallel_plan_of_dim 0` stores target dimension 0,
   `checked_parallelize_current` returns exactly that target as
   `certified_dim`, and `ParallelPolOpt` copies it unchanged into the codegen
   certificate (`driver/ParallelPolOpt.v:26-49`,
   `src/ParallelValidator.v:826-831`).  The command succeeds and emits a
   parallel loop, so this certificate path was accepted.
2. Both scheduled OpenScop statements have `SCATTERING 7 ...`; the seven rows
   are mapped one-for-one into `pi_schedule` by
   `from_openscop_sctt_to_pol_schedule` (`src/PolyLang.v:631-640`).  Therefore
   `CodeGen.complete_generate_many` computes `k = 7`.
3. Each statement reports six current iterators:
   `fk0 fk1 fk2 $i0 $i1 $i2`.
4. The observable raw generated nest contains loop variables `i0` through
   `i12`, exactly 13 coordinate levels: seven schedule-elimination coordinates
   followed by six reconstructed current coordinates.
5. The emitted annotation is:

   ```text
   parallel for i0 in range(0, ((32 + (B + -1)) / 32))
   ```

6. The reconstructed current dimension 0 occurs at raw syntactic depth seven:

   ```text
   for i7 in range(i0, (i0 + 1))
   ```

   The same singleton reconstruction appears in every relevant branch and is
   sequential.

The fixture is documented by `tools/parallel_current/README.md` as retaining
the checked raw singleton-loop form.  The retained `i7`-`i12` singleton loops
also make that path directly observable in the result.

## Static explanation

`complete_generate_many es n pis` computes `k`, applies
`PolyLang.elim_schedule k es`, and generates over `n+k` dimensions
(`polygen/CodeGen.v:97-100`).  `pi_elim_schedule` uses
`PSWInsertAfterEnv k`, so its point layout is:

```text
environment ; k schedule coordinates ; original current coordinates
```

(`src/PolyLang.v:7140-7149`).  At each recursive ASTGen level,
`generate_loop_many` projects the next coordinate after the environment and
wraps it in `PLoop` (`polygen/ASTGen.v:323-343`).  Thus, before cleanup, tag
depth `r < k` denotes schedule coordinate `r`; original current coordinate `d`
is reconstructed at depth `k+d`.

`ParallelCodegen.tag_loop_stmt_at 0` assigns tags by raw/cleaned syntactic depth
and `parallelize_dim` compares the certificate directly with that tag
(`src/ParallelCodegen.v:96-112`, `:403-429`).  There is no offset or semantic
origin map in this path.

## What this does and does not prove

This reproduction **proves a representation mismatch**: codegen tag 0 is the
first generated schedule coordinate, whereas validator dimension 0 is defined
over `current_coords_of` in the pre-codegen current view.  It does not by itself
show that this particular generated program is wrong.  In this fixture, the
first scattering row is exactly the first current coordinate (`fk0`), and the
singleton `i7 = i0` makes the relationship visible; the accepted annotation is
therefore plausible for this example.

A generic affine schedule can permute or mix current coordinates.  Existing
theorems do not prove that schedule coordinate `d` equals current coordinate
`d`, or that different values of generated loop `d` satisfy the validator's
`same_parallel_slice d` premise.  Hence the current certificate cannot justify
the annotation generically.

Changing the tag to `k+d` is not a complete fix: that targets the singleton
current-coordinate reconstruction loop, which is normally useless for
parallel execution and can disappear under cleanup.  A sound useful design
must either:

1. validate the actual generated schedule-loop coordinate and its outer
   schedule prefix; or
2. restrict and prove a mapping from the requested current dimension to a
   generated schedule dimension, then tag by that proved origin.

The cleaned path additionally requires an origin-remapping theorem because
singleton and constant loops are removed before tagging.
