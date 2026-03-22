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

Run the generated suite at the default `perf` tier with:

```bash
opam exec -- make test-end-to-end-generated
```

Other useful entry points:

```bash
opam exec -- make test-end-to-end-generated-smoke
opam exec -- make test-end-to-end-generated-heavy
opam exec -- make tune-end-to-end-generated
```
