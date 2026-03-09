# polcert

`polcert` is the validator-only executable.
It reads two polyhedral models in OpenScop format, converts both to the internal polyhedral representation with `from_openscop_complete`, and runs the verified validator.

This tool does **not** run extraction or code generation.
It is the direct CLI for the original PolCert validation story.

## When to use it

Use `polcert` when you already have two OpenScop files, typically:

- `before.scop`: the source schedule emitted by Pluto/Clan
- `after.scop`: the optimized schedule emitted by Pluto

and you want to check whether the schedule transformation is dependence-safe.

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

## What it validates

`polcert` checks schedule-preserving refinement/equivalence between two polyhedral models that share the same instruction/access structure and differ only by scheduling.
The validator constructs WAW/WAR/RAW dependence-checking polyhedra and rejects schedules that break Bernstein-style dependence preservation.

The top-level validation entrypoint is built from:

- [driver/TPolValidator.v](./driver/TPolValidator.v)
- [src/Validator.v](./src/Validator.v)
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

It does **not** prove correctness of:

- OpenScop textual parsing / printing implementation details
- Pluto itself
- any frontend from source code to OpenScop

## Notes

- `polcert` is intentionally unchanged by the recent `polopt` work.
- It remains the reference tool for validating two OpenScop models directly.
