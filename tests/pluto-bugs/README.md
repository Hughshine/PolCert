## Pluto Bug Reproducers

This directory is for artifact-grade Pluto bug or unsafe-hint reproducers.

Current cases:

- `matmul_parallel_hint`
  - Pluto's `--parallel` hint selects current dimension `0`
  - the checked PolCert parallel route rejects that dimension
  - the non-strict frontend falls back to certified current dimension `1`
  - the strict frontend keeps the loop sequential

Manual target:

```sh
opam exec -- make test-pluto-bug-matmul-parallel-hint
```

Background note:

- `doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md`
