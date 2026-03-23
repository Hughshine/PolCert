# Best Generated Perf Pipelines

This table records the current best measured `polopt` pipeline for each generated end-to-end perf case.

Notes:

- Baseline is always the unoptimized `input.loop` compiled into the same generated whole-C harness.
- Every selected optimized result goes through `polopt`; baseline is **not** eligible as a best pipeline.
- `identity` is only a last-resort `polopt --identity` fallback when all real optimization routes are slower.
- All selected best results currently have `exact_match=true`, `max_abs_diff=0.0`, and `max_rel_diff=0.0`.
- On this 62-case corpus, `iss` / `iss_parallel_4` means the `--iss` route measured best; it does **not** by itself prove that Pluto actually performed ISS statement splitting on that case.

## Pipeline Counts

- default no-ISS affine+tiling pipeline: `8`
- affine-only pipeline: `9`
- ISS-enabled sequential pipeline: `7`
- parallel route (4 threads): `20`
- ISS + parallel route (4 threads): `9`
- identity-only fallback: `9`

## Per-Case Table

| Case | Best pipeline | Flags | Speedup | Optimized time | Parallelized | Reason |
|---|---|---|---:|---:|---|---|
| 1dloop-invar | default no-ISS affine+tiling pipeline | (default) | 1.075x | 0.0011s | no | The default verified sequential route already wins; there is not enough structure here to justify heavier variants. |
| adi | identity-only fallback | `--identity` | 0.975x | 3.1687s | no | This wavefront-style kernel loses to more aggressive schedules at the chosen perf size, so the identity fallback is best. |
| advect3d | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.225x | 1.3073s | no | The `--parallel` route found a better sequential schedule, but no verified parallel loop was emitted. |
| corcol | affine-only pipeline | `--affine-only` | 4.032x | 0.4251s | no | Affine rescheduling is enough to improve locality; the extra tiling/parallel routes do not pay back here. |
| corcol3 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.886x | 0.4886s | yes | This case benefits from real outer-loop parallelism, so the verified 4-thread parallel route wins. |
| costfunc | default no-ISS affine+tiling pipeline | (default) | 1.466x | 0.7711s | no | The default no-ISS affine+tiling route already gives the best sequential trade-off on this recurrence-heavy case. |
| covcol | affine-only pipeline | `--affine-only` | 4.274x | 0.4121s | no | Affine-only blocking/reordering gives the best locality here; the richer routes add overhead. |
| dct | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.015x | 3.6192s | no | The ISS+parallel route wins only as an alternate sequential schedule; it did not emit a verified parallel loop. |
| doitgen | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.968x | 1.9920s | yes | This dense kernel has profitable outer-loop parallelism, and the verified parallel route exposes it cleanly. |
| dsyr2k | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 2.443x | 2.1830s | yes | This is a real parallel win: the selected route emits `parallel for`, and the speedup appears only once multiple threads are used. |
| dsyrk | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 2.082x | 1.8748s | yes | Another dense linear-algebra kernel with real outer-loop parallelism; the verified parallel route is clearly best. |
| fdtd-1d | identity-only fallback | `--identity` | 1.051x | 2.1839s | no | Single-thread performance is best when the original loop shape is preserved; skewed or tiled variants hurt at this size. |
| fdtd-2d | identity-only fallback | `--identity` | 1.021x | 3.7360s | no | The more aggressive schedules are profitable for wavefront parallelism, not for this single-thread perf tier, so identity wins. |
| floyd | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.073x | 1.7516s | no | The ISS+parallel route produced the fastest sequential schedule here, but there is no evidence of actual ISS splitting or emitted parallelism on this corpus. |
| fusion1 | identity-only fallback | `--identity` | 1.072x | 0.0038s | no | This case is too small/lightweight for the current optimization overheads to pay off, so identity is safest. |
| fusion10 | ISS-enabled sequential pipeline | `--iss` | 1.158x | 0.0013s | no | The ISS-enabled route measured best, but this is a tiny case and there is no evidence that true ISS splitting fired here. |
| fusion2 | affine-only pipeline | `--affine-only` | 1.343x | 0.0012s | no | Affine reordering helps, but the default tiled route is not the best trade-off on this small fusion kernel. |
| fusion3 | affine-only pipeline | `--affine-only` | 1.636x | 0.6195s | no | Affine-only fusion/reordering wins without needing the heavier routes. |
| fusion4 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.558x | 0.6530s | no | The `--parallel` route wins as a better sequential schedule; no verified parallel loop was emitted. |
| fusion5 | affine-only pipeline | `--affine-only` | 1.426x | 0.3230s | no | Affine-only scheduling is enough to improve this fusion case; the extra routes do not help further. |
| fusion6 | default no-ISS affine+tiling pipeline | (default) | 1.072x | 0.0037s | no | The default no-ISS affine+tiling pipeline remains the best cached result for this case. |
| fusion7 | default no-ISS affine+tiling pipeline | (default) | 1.114x | 0.0027s | no | The default no-ISS affine+tiling pipeline already provides the best measured result. |
| fusion8 | ISS-enabled sequential pipeline | `--iss` | 1.175x | 0.0010s | no | The ISS-enabled route measures best, but the benchmark is small and this should be read as a pipeline-level win, not confirmed ISS splitting. |
| fusion9 | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 14.534x | 0.0992s | yes | The best result comes from the ISS+parallel route with real emitted parallelism; the dominant gain is parallel execution, not confirmed ISS splitting. |
| gemver | affine-only pipeline | `--affine-only` | 1.472x | 0.9813s | no | Affine-only scheduling helps producer-consumer locality here; the extra routes are unnecessary. |
| intratileopt1 | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.856x | 0.8325s | yes | The ISS+parallel route emits real parallelism and wins, though the benefit is smaller than on the denser BLAS-like kernels. |
| intratileopt2 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.821x | 0.8414s | yes | Real parallelism is profitable here, so the 4-thread verified parallel route is best. |
| intratileopt3 | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.448x | 1.7265s | yes | The ISS+parallel route emits real parallelism and edges out the alternatives. |
| intratileopt4 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 2.553x | 0.3978s | yes | This case still prefers the verified parallel route, but the gain is modest compared with the larger dense kernels. |
| jacobi-1d-imper | identity-only fallback | `--identity` | 1.041x | 1.6811s | no | At this perf size, skewing/tiling overheads dominate, so the identity fallback is still fastest. |
| jacobi-2d-imper | identity-only fallback | `--identity` | 1.025x | 1.8829s | no | This stencil prefers the original sequential loop shape at the chosen perf tier; transformed variants are slower. |
| lu | identity-only fallback | `--identity` | 0.990x | 2.9326s | no | The triangular dependence structure does not benefit from the tested transformed routes at this size, so identity wins. |
| matmul | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.705x | 0.3442s | yes | A real parallel win: the selected route emits `parallel for` and gives a strong speedup on a dense blocked kernel. |
| matmul-init | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 4.792x | 0.2733s | yes | The verified parallel route wins by parallelizing a regular dense kernel with good outer-loop work sharing. |
| matmul-seq | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.017x | 2.5048s | no | The `--parallel` route is best here as an alternate sequential schedule; it does not actually emit parallel code. |
| matmul-seq3 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.002x | 3.7675s | no | This case is rescued by the `--parallel` scheduling path, but not by actual emitted parallelism. |
| multi-loop-param | ISS-enabled sequential pipeline | `--iss` | 1.302x | 0.0027s | no | The ISS-enabled route happened to measure best, but this remains a tiny-case pipeline choice rather than clear ISS activity. |
| multi-stmt-stencil-seq | identity-only fallback | `--identity` | 1.366x | 0.0057s | no | This small stencil-like case still prefers the original schedule at the perf tier used here. |
| mvt | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 2.037x | 0.4368s | yes | The ISS+parallel route emits real parallelism and is the fastest option on this two-kernel benchmark. |
| mxv | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.205x | 1.5397s | yes | This matrix-vector case gets a real, but smaller, benefit from verified parallelization. |
| mxv-seq | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.053x | 1.5063s | no | The `--parallel` route wins by choosing a better sequential schedule; no verified parallel loop was emitted. |
| mxv-seq3 | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.330x | 1.0375s | no | Again the gain comes from the alternate `--parallel` scheduling path, not from actual parallel execution. |
| negparam | affine-only pipeline | `--affine-only` | 1.220x | 0.0011s | no | Affine-only scheduling gives the best result; the richer routes are not worthwhile here. |
| nodep | ISS-enabled sequential pipeline | `--iss` | 1.255x | 0.0010s | no | The ISS-enabled route measures best on this tiny dependence-free case, but there is no evidence of actual ISS splitting. |
| noloop | default no-ISS affine+tiling pipeline | (default) | 1.298x | 0.0011s | no | The default no-ISS affine+tiling pipeline is effectively just the best cached default route here. |
| pca | default no-ISS affine+tiling pipeline | (default) | 1.799x | 0.5571s | no | The default verified sequential route remains the best measured choice on this benchmark. |
| polynomial | identity-only fallback | `--identity` | 0.995x | 3.4667s | no | This streaming/reduction kernel is hurt by the current transformed variants, so identity remains the best available `polopt` route. |
| seidel | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.089x | 3.3846s | no | The ISS+parallel route wins only as a different sequential schedule; it does not emit a verified parallel loop here. |
| seq | default no-ISS affine+tiling pipeline | (default) | 1.369x | 1.9029s | no | The default no-ISS affine+tiling pipeline already gives the best measured sequential result. |
| shift | affine-only pipeline | `--affine-only` | 1.075x | 0.9055s | no | Affine-only scheduling is the best trade-off; heavier routes do not improve this simple shift kernel. |
| spatial | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 1.336x | 1.7358s | yes | The ISS+parallel route emits real parallelism and wins, although the gain is moderate. |
| ssymm | ISS + parallel route (4 threads) | `--iss --parallel` + `OMP_NUM_THREADS=4` | 14.735x | 0.3160s | yes | This is one of the strongest real parallel wins; the ISS+parallel route emits `parallel for` and scales very well. |
| strmm | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 5.068x | 1.0648s | yes | The verified parallel route is clearly best on this dense triangular matrix kernel. |
| strsm | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 7.814x | 0.9731s | yes | Another strong real parallel win: the 4-thread verified route is much faster than the sequential alternatives. |
| tce | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 1.139x | 3.1639s | no | The `--parallel` route wins as a better sequential schedule; it did not emit parallel code on this case. |
| tmm | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 3.407x | 2.2072s | yes | This dense matrix kernel gets a strong real gain from verified parallelization. |
| tricky1 | affine-only pipeline | `--affine-only` | 1028.805x | 0.0019s | no | Affine-only scheduling is decisively best on this synthetic case; the richer routes add no value. |
| tricky2 | ISS-enabled sequential pipeline | `--iss` | 1.208x | 0.0011s | no | The ISS-enabled route wins on a very small synthetic case, but this should not be overinterpreted as confirmed ISS splitting. |
| tricky3 | ISS-enabled sequential pipeline | `--iss` | 1.169x | 0.0011s | no | Same story as `tricky2`: ISS-route win, but on a tiny case without evidence of real ISS activity. |
| tricky4 | ISS-enabled sequential pipeline | `--iss` | 1.121x | 0.0011s | no | Again the ISS-enabled route wins only as a small-case pipeline choice, not confirmed ISS splitting. |
| trisolv | parallel route (4 threads) | `--parallel` + `OMP_NUM_THREADS=4` | 5.673x | 0.2233s | yes | This is a real parallel win with a strong speedup from the verified 4-thread route. |
| wavefront | default no-ISS affine+tiling pipeline | (default) | 1.514x | 1.7204s | no | The default no-ISS affine+tiling pipeline remains the best cached sequential result on this benchmark. |

