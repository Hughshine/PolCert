# Automatic Affine LP Component Scaling

Status: reproduced, minimized, validator-catches, automatic-scheduler case.

This fixture does not provide `.fst`, `.precut`, `skipdeps.txt`, a schedule, or
any other control file. Pluto computes the affine schedule itself with its GLPK
LP scheduler. Parallelization, tiling, vectorization, unroll-jam, intra-tile
optimization, and diamond tiling are disabled.

The four statements form two dependence components whose statement identifiers
are interleaved: `{S1,S3}` and `{S2,S4}`. Pluto's connected-component pass
overwrites the component identifier of an already visited vertex. LP schedule
integerization then scales the two ends of the `S3 -> S1` dependence by
different factors and produces an illegal affine schedule.

On the pinned Pluto revision, the source prints `802469374803681347`, while
Pluto's generated program prints `11412027514774867379`. PolCert's standalone
affine checker rejects the exact before/after OpenScop pair with `overall:
FAIL`.

The complete PolCert driver adds read-after-read dependences with `--rar`.
For this source shape, that changes Pluto's optimization problem and it returns
a different, legal candidate. Therefore this fixture claims rejection of the
exact bad phase-dump pair at the affine validation boundary; it does not claim
that the complete driver receives the same candidate.

Run:

```sh
opam exec -- make test-pluto-miscompilation-auto-affine-lp
```
