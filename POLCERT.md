# polcert

`polcert` is the validator-only executable.
It reads polyhedral models, converts them to the internal representation, and
runs the verified validator stack.

This tool does **not** run extraction or code generation.
It is the direct CLI for the PolCert validation story, which now includes:

- the original affine validation route
- the phase-aligned checked tiling route
- ISS structural validation through Pluto bridge / debug-dump inputs

## When to use it

Use `polcert` when you already have transformation results and want to validate
them without running the optimizer frontend.

There are now four common validation modes:

1. direct affine validation of a single `before.scop -> after.scop`
2. phase-aligned validation of
   - `before -> mid` using the affine validator
   - `mid -> after` using the checked tiling validator
3. tiling-only validation of `mid.scop -> after.scop`
4. ISS structural validation through:
   - `--iss-bridge`
   - `--iss-debug-dumps`

This CLI surface is about the affine / ordinary-tiling OpenScop story plus the
ISS bridge story. The newer diamond pipeline and parallel codegen routes live
on the `polopt` side; they are not exposed as separate `polcert` user modes.

## CLI shapes

OpenScop modes:

```sh
./polcert before.scop after.scop
./polcert --kind tiling mid.scop after.scop
./polcert before.scop mid.scop after.scop
```

ISS modes:

```sh
./polcert --iss-bridge bridge.txt
./polcert --iss-debug-dumps before.txt after.txt
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

Run Pluto with the repository's standard affine-scheduling flags:

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

In other words, `polcert` still validates the OpenScop-facing affine/tiling
artifacts directly. It does not currently expose the internal post-tile/final
affine split that the diamond `polopt` harness reasons about.

ISS is different:

- it is not currently validated through OpenScop
- it uses a Pluto-derived bridge / dump interface instead
- this matches the fact that Pluto ISS is implemented over Pluto's internal
  program representation rather than the old OpenScop-only path

## What it validates

For the affine route, `polcert` checks schedule-preserving
refinement/equivalence between two polyhedral models that share the same
instruction/access structure and differ only by scheduling.

For the tiling route, it checks:

1. a structural tiling/witness relation
2. a canonical imported tiled program
3. the generic schedule/dependence validator on that imported program

For the ISS route, it checks a structural split relation centered on Pluto ISS
bridge / dump inputs rather than OpenScop.

The top-level validation entrypoints are built from:

- [driver/TPolValidator.v](./driver/TPolValidator.v)
- [src/Validator.v](./src/Validator.v)
- [src/TilingValidator.v](./src/TilingValidator.v)
- [src/PolyLang.v](./src/PolyLang.v)
- [src/ISSValidator.v](./src/ISSValidator.v)
- [src/ISSValidatorCorrect.v](./src/ISSValidatorCorrect.v)

## Result meanings

- `EQ`: the two models are mutually equivalent
- `LT` / `GT`: one model refines the other in only one direction
- `NE`: the validator cannot prove a refinement relation

For ISS CLI modes, success/failure is reported directly as bridge/dump
validation output rather than `EQ/LT/GT/NE`.

## Proof boundary

The verified part covers:

- the validator algorithms themselves
- the polyhedral semantics they reason about
- the soundness theorems relating successful validation to semantic
  refinement/equivalence
- the checked tiling validator route
- the checked ISS structural validator route

It does **not** prove correctness of:

- OpenScop textual parsing / printing implementation details
- Pluto itself
- witness inference heuristics
- any frontend from source code to OpenScop

It also does not currently expose a user-facing parallel validation mode; the
parallel story currently lives on the `polopt` side.

## Notes

- `polcert` still serves as the direct validator for OpenScop affine / tiling
  models.
- It now also exposes ISS structural validation modes, but those use Pluto
  bridge / debug-dump inputs rather than OpenScop.
- For a concise overview of how the affine, tiling, and ISS validation routes
  fit together, see [doc/VERIFIED_PIPELINE.md](./doc/VERIFIED_PIPELINE.md) and
  [doc/FEATURE_STATUS.md](./doc/FEATURE_STATUS.md).
