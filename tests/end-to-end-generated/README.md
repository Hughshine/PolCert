# generated end-to-end suite

This directory hosts the synthesized whole-C benchmark path for the generated
`polopt` regression corpus under `tests/polopt-generated/cases/*`.

Unlike the handwritten harnesses in `tests/end-to-end-c/cases/*`, this suite
does not rely on benchmark-specific wrappers. Instead it:

- reads `input.loop` and `optimized.loop`
- synthesizes complete C programs with deterministic parameter values
- declares and initializes all discovered arrays/scalars
- recompiles baseline and optimized executables
- compares their numeric summaries
- records end-to-end runtime for each case

This provides uniform whole-program coverage for the full generated corpus,
including fragmentary benchmarks that do not have a reusable original C driver.

The suite now supports parameter tiers through
`tests/end-to-end-generated/param_tiers.json`:

- `smoke`: conservative quick-check sizes
- `perf`: tuned toward roughly second-scale runtimes when practical
- `heavy`: one step above `perf` when a larger stable point was found

It also supports an on-the-fly optimization mode driven by `polopt`, which is
useful for benchmarking `--parallel` output without first materializing a new
`optimized.loop`. When that mode emits `parallel for`, the generated C is
compiled with OpenMP and run with the requested `OMP_NUM_THREADS`.

Run the generated suite at the default `perf` tier with:

```bash
opam exec -- make test-end-to-end-generated
```

Other useful entry points:

```bash
opam exec -- make test-end-to-end-generated-smoke
opam exec -- make test-end-to-end-generated-heavy
opam exec -- make test-end-to-end-generated-perf-parallel
opam exec -- make test-end-to-end-generated-slow-perf-parallel
opam exec -- make tune-end-to-end-generated
```
