# polcert

`polcert` is the validator-only executable.
It reads two polyhedral models in OpenScop format, converts both to the internal polyhedral representation with `from_openscop_complete`, and runs the verified validator.

This tool does **not** run extraction or code generation.
It is the direct CLI for the PolCert validation story, which now includes both
the original affine validation route and the phase-aligned checked tiling route.

## When to use it

Use `polcert` when you already have two OpenScop files, typically:

- `before.scop`: the source schedule emitted by Pluto/Clan
- `after.scop`: the optimized schedule emitted by Pluto

and you want to check whether the schedule transformation is dependence-safe.

There are now two common validation modes:

1. direct validation of a single `before.scop -> after.scop` schedule change
2. phase-aligned validation of
   - `before -> mid` using the affine validator
   - `mid -> after` using the checked tiling validator

There is also a tiling-only CLI mode:

```sh
./polcert --kind tiling mid.scop after.scop
```

## Typical user workflow: C fragment -> Pluto -> polcert

Write a C loop fragment surrounded by `#pragma scop`.
For example:

```c
#pragma scop
for (j1 = 1; j1 <= M; j1++) {
  for (j2 = j1; j2 <= M; j2++) {
    for (i = 1; i <= N; i++) {
      symmat[j1][j2] = symmat[j1][j2] + data[i][j1] * data[i][j2];
    }
    symmat[j2][j1] = symmat[j1][j2];
  }
}
#pragma endscop
```

Run Pluto with the repository's standard flags:

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
      --smartfuse --nounrolljam --noparallel --notile --rar test.c
```

This produces:

```text
test.beforescheduling.scop
test.afterscheduling.scop
```

Then validate:

```sh
./polcert test.beforescheduling.scop test.afterscheduling.scop
```

Typical output:

```text
[EQ] The two polyhedral models ... are equivalent.
```

For the phase-aligned tiling route, the common workflow is instead:

1. run Pluto phase 1 to obtain `mid.scop`
2. run Pluto phase 2 tiling to obtain `after.scop`
3. validate either:
   - only `mid -> after` with `--kind tiling`
   - or the full `before, mid, after` phase-aligned route

## What it validates

For the affine route, `polcert` checks schedule-preserving
refinement/equivalence between two polyhedral models that share the same
instruction/access structure and differ only by scheduling.

For the tiling route, it checks:

1. a structural tiling/witness relation
2. a canonical imported tiled program
3. the generic schedule/dependence validator on that imported program

The top-level validation entrypoint is built from:

- [driver/TPolValidator.v](./driver/TPolValidator.v)
- [src/Validator.v](./src/Validator.v)
- [src/TilingValidator.v](./src/TilingValidator.v)
- [src/PolyLang.v](./src/PolyLang.v)

## Result meanings

- `EQ`: the two models are mutually equivalent
- `LT` / `GT`: one model refines the other in only one direction
- `NE`: the validator cannot prove a refinement relation

## Proof boundary

The verified part covers:

- the validator algorithm itself
- the polyhedral semantics it reasons about
- the soundness theorem relating successful validation to semantic refinement/equivalence
- the checked tiling validator route used for phase-aligned tiling validation

It does **not** prove correctness of:

- OpenScop textual parsing / printing implementation details
- Pluto itself
- witness inference heuristics
- any frontend from source code to OpenScop

## Notes

- `polcert` still serves as the direct validator for OpenScop models.
- It now also exposes the checked tiling route used by the verified optimizer.
- For a concise overview of how the affine and tiling validation routes fit
  together, see [doc/VERIFIED_PIPELINE.md](./doc/VERIFIED_PIPELINE.md).
