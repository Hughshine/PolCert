# Parallel-Current Suite

This suite exercises the theorem-facing `--parallel-current <dim>` entry points.
The legacy option name now selects a padded schedule coordinate.  The suite
checks that the extracted validator certifies that coordinate and that parallel
code generation marks the corresponding generated loop with `parallel for`.

The `diamond-current-combined-effect` case is the positive diamond witness. The fixture `diamond-example-inner-batch.loop` is a single-statement stencil based on Pluto's diamond-tile example, with an independent batch dimension `B`. The command

```sh
./polopt --diamond-tile --parallel-current 0 tools/parallel_current/fixtures/diamond-example-inner-batch.loop
```

must emit `parallel for`, 32-sized tile expressions, and the diagonal expression `i4 + (-1 * i5)`. The diagonal expression is the useful witness: it shows that the output is not just rectangular tiling over `t` and `i`, but a skewed diamond schedule where one source index is reconstructed from coupled schedule coordinates.

The `diamond-current-jacobi-batch-positive` case covers the wider two-statement Jacobi shape. Batched Jacobi exposes the same independent batch dimension, while the diamond schedule introduces parity guards and singleton reconstruction loops. The command

```sh
./polopt --diamond-tile --parallel-current 0 tools/parallel_current/fixtures/jacobi-batch.loop
```

must emit `parallel for`, coupled diamond expressions such as `64 *` and `(-2 * i11)`, and both `a` and `b` updates. This case retains the checked standard-raw singleton-loop codegen form because one of the proof-relevant cleanup stages is not trace-safe. The raw form passes its own trace-safety check and remains on the same verified codegen route.
