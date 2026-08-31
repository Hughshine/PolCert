# Direct Pluto Unroll-Jam Effect Corpus

This report compares native Pluto `--unrolljam` against native Pluto `--nounrolljam` on extracted OpenScop, then checks whether the affine-validated `polopt --pluto-compat --notile --unrolljam` route produces a corresponding checked Loop-IR structure.

A case counts as a direct Pluto codegen effect only when the two native Pluto after-scheduling OpenScop files are identical, the generated C differs, and the unrolled native C contains the requested factor step. PolOpt coverage is structural: its output must contain the same block factor and the final intra-block offset. The PolOpt side deliberately disables tiling, and any tiling-validation route report fails this check, so the result isolates the Loop-level unroll-jam implementation from tiling acceptance. The extracted sequential endpoint covers constant and block unrolling, locally validated jam, recursive composition, and cleanup.

## Summary

- cases: 11
- extract_failures: 0
- pluto_failures: 0
- native_codegen_effects: 6
- native_effects_covered: 6
- native_effects_uncovered: 0
- polopt_tiling_route_reports: 0
- polopt_extra_checked_effects_without_native: 0
- native_no_effect: 5

## Cases

| Fixture | Pluto clean codegen effect | PolOpt checked effect | Covered | Note |
|---|---:|---:|---:|---|
| `tests/polopt-generated/inputs/matmul.loop` | yes | yes | yes | native effect covered by checked PolOpt structure |
| `tests/polopt-generated/inputs/matmul-init.loop` | yes | yes | yes | native effect covered by checked PolOpt structure |
| `tests/polopt-generated/inputs/matmul-seq.loop` | yes | yes | yes | native effect covered by checked PolOpt structure |
| `tests/polopt-generated/inputs/mxv.loop` | yes | yes | yes | native effect covered by checked PolOpt structure |
| `tests/polopt-generated/inputs/mxv-seq.loop` | yes | yes | yes | native effect covered by checked PolOpt structure |
| `tests/polopt-generated/inputs/nodep.loop` | no | no | yes | native Pluto shows no direct unroll-jam C effect |
| `tests/polopt-generated/inputs/fusion1.loop` | no | no | yes | native Pluto shows no direct unroll-jam C effect |
| `tests/polopt-generated/inputs/fusion2.loop` | no | no | yes | native Pluto shows no direct unroll-jam C effect |
| `tests/polopt-generated/inputs/fusion7.loop` | no | no | yes | native Pluto shows no direct unroll-jam C effect |
| `tests/polopt-generated/inputs/fdtd-1d.loop` | yes | yes | yes | native effect covered by checked PolOpt structure |
| `tests/polopt-generated/inputs/jacobi-1d-imper.loop` | no | no | yes | native Pluto shows no direct unroll-jam C effect |
