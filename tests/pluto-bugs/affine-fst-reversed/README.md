# Reversed Affine Statement Order

Status: reproduced, minimized, validator-catches.

The source loop writes `a[i]` and then copies that value to `b[i]`. The
`reversed.fst` control file assigns the consumer statement to scalar group `0`
and the producer to group `1`. Pluto installs that order before affine
scheduling and later marks the dependence satisfied on a positive loop
coordinate, without rejecting the earlier negative scalar coordinate.

At pinned Pluto commit `56b66690edeed1ef17ddc018bbf67666795a3fd4`,
the generated program runs the complete `b` loop before the `a` loop. The
original prints `100`; Pluto's output prints `0`.

PolCert rejects the same schedule at both useful interfaces:

- `--validate-affine-openscop` reports `overall: FAIL` for Pluto's before/after
  OpenScop pair;
- the Pluto-compatible route with `--fusion-structure reversed.fst` raises an
  alarm and emits no optimized Loop.

Run the producer, executable comparison, and both checked rejections with:

```sh
opam exec -- make test-pluto-miscompilation-affine-fst
```
