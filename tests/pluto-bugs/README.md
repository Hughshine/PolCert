## Pluto Bug Reproducers

This directory is for artifact-grade Pluto bug or unsafe-hint reproducers.

Current cases:

- `auto-affine-lp-cc-scaling` (confirmed automatic-scheduler miscompilation)
  - Pluto's GLPK LP scheduler computes the schedule without a supplied control
    file or schedule
  - incorrect DDG component relabeling lets LP integerization scale the two
    ends of a dependence independently
  - the source and Pluto output print different checksums
  - PolCert's affine validator rejects the exact bad before/after schedule
  - the default no-RAR complete route rejects the corresponding `.loop`
    candidate, while explicit `--rar` obtains and accepts a different legal one
- `diamond-nointratile-reschedule` (fixed pure-tiling miscompilation)
  - a phase-dump patch incorrectly made a mandatory diamond hyperplane restore
    conditional on the optional intra-tile locality pass
  - the original printed `20`; diamond/no-intratile printed `18`, and
    full-diamond/no-intratile printed `15`
  - the fixed Pluto baseline prints `20`; PolCert rejects the corresponding
    mixed-scalar candidate and emits no optimized loop
  - the independent typed `diamond-stencil` positive case confirms supported
    pure diamond tiling and post-affine code generation are accepted
- `affine-fst-reversed` (confirmed control-interface miscompilation)
  - a forced scalar schedule places the consumer before its producer
  - the original prints `100`, while Pluto's output prints `0`
  - with the honest Pluto domain/access summaries, the standalone schedule
    validator and complete compatibility route reject it
  - this deliberately inconsistent `.fst` file does not demonstrate that
    Pluto's automatic affine scheduler discovers an illegal schedule
- `matmul_parallel_hint` (parallel-hint coordinate-mapping regression)
  - with explicitly requested `--rar`, Pluto's `--parallel` hint names raw
    scattering row `1`
  - the checked PolCert route maps and certifies canonical coordinate `1`
  - strict and non-strict frontends both parallelize the intended loop
- `vanished-outer-parallel` (confirmed silent miscompilation)
  - Pluto marks an independent one-trip outer schedule coordinate parallel
  - CLooG removes that constant coordinate
  - Pluto's AST fallback transfers the annotation to a dependent inner loop
  - the original prints `10000`, while the OpenMP output differs
  - PolCert maps the hint to its canonical singleton coordinate, while a direct
    check of the dependent inner coordinate rejects it
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
  - PolCert accepts the legal tiling and the mapped singleton coordinate, but
    never applies the unsafe nontrivial parallel overlay

Run all cases:

```sh
opam exec -- make test-pluto-bugs
```

Artifact version policy:

- ordinary PolOpt and Pluto compatibility tests use the fixed Pluto checkout
  at `/pluto`;
- the five active producer miscompilations use only the pinned historical
  checkout at `/opt/polcert/pluto-buggy`;
- the fixed diamond regression and the matmul hint-mapping check use the normal
  fixed checkout;
- a missing historical checkout is an error, not a fallback to `/pluto`.

The two Pluto revisions are checked by `tools/ci/check_pluto_baseline.sh` and
recorded separately in `BUILD_PROVENANCE.json`.

Background note:

- `doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md`
- `doc/pluto-whitebox-correctness-audit.md`
- `doc/pluto-upstream-miscompilation-report-draft.md`

ISS adversarial bridge fixtures live in `tests/iss-pluto-dumps/`. Pluto's
multi-cut bookkeeping mismatch is not labeled a numerical miscompilation: the
current checked route reconstructs cuts from the actual split domains and the
complete-cut checker rejects inconsistent or incomplete witnesses.
