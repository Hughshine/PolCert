## Pluto Bug Reproducers

This directory is for artifact-grade Pluto bug or unsafe-hint reproducers.

Current cases:

- `matmul_parallel_hint` (unsafe hint, not a demonstrated raw-Pluto miscompile)
  - Pluto's `--parallel` hint selects current dimension `0`
  - the checked PolCert parallel route rejects that dimension
  - the non-strict frontend falls back to certified current dimension `1`
  - the strict frontend keeps the loop sequential
- `vanished-outer-parallel` (confirmed silent miscompilation)
  - Pluto marks an independent one-trip outer schedule coordinate parallel
  - CLooG removes that constant coordinate
  - Pluto's AST fallback transfers the annotation to a dependent inner loop
  - the original prints `10000`, while the OpenMP output differs
  - both PolCert's strict hint route and direct inner-loop check reject it
- `notile-unrolljam-nonpermutable` (confirmed silent miscompilation)
  - Pluto's no-tile candidate search skips the real outer-band boundary
  - it jams a dependence-carrying `j` loop into the inner `k` loop
  - the original prints `15`, while Pluto's output prints `1`
  - PolCert unrolls the candidate but rejects the unsafe jam, preserving two
    separate inner `k` loops

Run all cases:

```sh
opam exec -- make test-pluto-bugs
```

Background note:

- `doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md`
- `doc/pluto-whitebox-correctness-audit.md`
