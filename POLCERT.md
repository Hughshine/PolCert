# polcert

`polcert` is the validator-only executable.
It reads two polyhedral models in OpenScop format, converts both to the internal polyhedral representation with `from_openscop_complete`, and runs the verified validator.

This tool does **not** run extraction or code generation.
It is the direct CLI for the original PolCert validation story.

## What it validates

`polcert` checks schedule-preserving refinement/equivalence between two polyhedral models that share the same instruction/access structure and differ only by scheduling.
The validator constructs WAW/WAR/RAW dependence-checking polyhedra and rejects schedules that break Bernstein-style dependence preservation.

The top-level validation entrypoint is built from:

- [driver/TPolValidator.v](./driver/TPolValidator.v)
- [src/Validator.v](./src/Validator.v)
- [src/PolyLang.v](./src/PolyLang.v)

## Proof boundary

The verified part covers:

- the validator algorithm itself
- the polyhedral semantics it reasons about
- the soundness theorem relating successful validation to semantic refinement/equivalence

It does **not** prove correctness of:

- OpenScop textual parsing / printing implementation details
- Pluto itself
- any frontend from source code to OpenScop

## Build and run

Build inside the project container with the standard sequence from [README.md](./README.md).
Then run:

```sh
./polcert before.scop after.scop
```

Typical workflow:

1. Produce `before.scop` and `after.scop` with Pluto:

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
      --smartfuse --nounrolljam --noparallel --notile --rar test.c
```

2. Validate the result:

```sh
./polcert test.beforescheduling.scop test.afterscheduling.scop
```

## Notes

- `polcert` is intentionally unchanged by the recent `polopt` work.
- It remains the reference tool for validating two OpenScop models directly.
