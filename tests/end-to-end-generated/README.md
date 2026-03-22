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

Run the full generated suite with:

```bash
opam exec -- make test-end-to-end-generated
```
