# Vanished outer parallel loop

Status: reproduced, minimized, validator-catches.

The outer `i` loop has exactly one iteration and is independent.  The inner
`j` loop carries the recurrence `a[0][j - 1] -> a[0][j]` and must remain
sequential.

At the pinned bug-reproduction commit
`historical-bug-witness-pluto-snapshot`,
the affine schedule is `(0, j)`.  CLooG therefore removes the constant outer
schedule coordinate.  `tool/ast_transform.c:75-95` then searches inward for a
loop on which to place the parallel annotation.  Its band-boundary test uses
`>` where the half-open band boundary requires `>=`, so it crosses a width-one
parallel band and marks the dependent `j` loop parallel. The ordinary fixed
Pluto baseline `ordinary-fixed-pluto-snapshot` keeps the search inside the half-open band boundary.

The raw Pluto command succeeds and produces an OpenMP program:

```sh
polycc --notile --nodiamond-tile --nointratileopt --noprevector \
  --nounrolljam --parallel vanished_outer_parallel.c
```

With four OpenMP threads, the original program prints `10000`; the generated
program prints a different value.  This is a silent miscompilation, not merely
an imprecise hint or a missed optimization.

PolCert handles both relevant boundaries defensively:

- `--parallel --parallel-strict` maps Pluto's `t1` metadata to its canonical
  one-iteration coordinate and does not transfer the annotation inward.
- `--notile --parallel-current 1` directly checks the actual inner loop chosen
  by Pluto's AST fallback and rejects it because it carries a dependence.

Run the complete reproducer with:

```sh
opam exec -- make test-pluto-miscompilation-vanished-outer
```
