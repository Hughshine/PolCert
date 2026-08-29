## Pluto Bug Reproducers

This directory is for artifact-grade Pluto bug or unsafe-hint reproducers.

Current cases:

- `diamond-nointratile-reschedule` (fixed pure-tiling miscompilation)
  - a phase-dump patch incorrectly made a mandatory diamond hyperplane restore
    conditional on the optional intra-tile locality pass
  - the original printed `20`; diamond/no-intratile printed `18`, and
    full-diamond/no-intratile printed `15`
  - the fixed Pluto baseline prints `20`; PolCert rejects the corresponding
    mixed-scalar candidate and emits no optimized loop
  - the independent typed `diamond-stencil` positive case confirms supported
    pure diamond tiling and post-affine code generation are accepted
- `affine-fst-reversed` (confirmed silent miscompilation)
  - a forced scalar schedule places the consumer before its producer
  - the original prints `100`, while Pluto's output prints `0`
  - with the honest Pluto domain/access summaries, the standalone schedule
    validator and complete compatibility route reject it
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
- `tiling-innerpar-satvec` (confirmed silent miscompilation)
  - Pluto's `--innerpar` path clears a dependence bit without changing schedule
  - the resulting OpenMP tiled program produces values that differ from the
    original recurrence
  - PolCert accepts the legal tiling boundary but rejects the unsafe parallel
    overlay

Run all cases:

```sh
opam exec -- make test-pluto-bugs
```

Background note:

- `doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md`
- `doc/pluto-whitebox-correctness-audit.md`
- `doc/pluto-upstream-miscompilation-report-draft.md`

ISS adversarial bridge fixtures live in `tests/iss-pluto-dumps/`. Pluto's
multi-cut bookkeeping mismatch is not labeled a numerical miscompilation: the
current checked route reconstructs cuts from the actual split domains and the
complete-cut checker rejects inconsistent or incomplete witnesses.
