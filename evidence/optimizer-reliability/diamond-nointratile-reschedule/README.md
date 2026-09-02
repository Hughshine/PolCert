# Diamond tiling without intra-tile optimization

The phase-dump patch at Pluto commit `diamond-regression-introduction-snapshot` accidentally guarded
`pluto_diamond_tile_reschedule` with `options->intratileopt`; the regression
remained present at audited predecessor `diamond-regression-snapshot`. That reschedule restores the
hyperplane temporarily evicted to construct a concurrent-start diamond
schedule. It is required for Pluto's final CLooG/AST path; it is not the
optional intra-tile locality pass controlled by `--intratileopt`.

With tile size `2` and every non-tiling optimization disabled, the original
`diamond_nointratile.c` prints `20`. The old `--diamond-tile
--nointratileopt` path printed `18`; full-diamond printed `15`. Ordinary and
two-level rectangular tiling both printed `20`. ASan and UBSan report no error,
so this is an execution-order defect rather than undefined behavior in the
fixture.

Pluto commit `diamond-fix-snapshot` on `diamond-fix-branch` makes the
restore unconditional for diamond tiling and adds the same executable
regression; this fix is not yet on `historical-phase-dump-branch`. The PolCert regression
checks both the fixed raw producer and the corresponding mixed-scalar `.loop`
candidate. PolCert's formal tiling boundary rejects that candidate and emits
no optimized loop. This rejection is conservative: the producer/backend
defect is the missing mandatory restore, while the formal checker independently
declines the degenerate scalar tile link. The separate typed `diamond-stencil`
positive test demonstrates that a supported pure diamond candidate is accepted
through checked tiling, post-tiling affine validation, and proved code
generation.

The ordinary artifact baseline `ordinary-fixed-pluto-snapshot` contains this earlier fix. The
historical `historical-bug-witness-pluto-snapshot` checkout is retained separately for the old failing
producer and is never used by ordinary PolOpt tests.
