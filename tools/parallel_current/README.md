# Parallel-Current Suite

This suite exercises the theorem-facing `--parallel-current <dim>` entry points. It checks that the extracted validator can certify an explicit current-space dimension and that parallel code generation marks that dimension with `parallel for`.

The `diamond-current-combined-effect` case is the positive diamond witness. The fixture `diamond-example-inner-batch.loop` is a single-statement stencil based on Pluto's diamond-tile example, with an independent batch dimension `B`. The command

```sh
./polopt --diamond-tile --parallel-current 0 tools/parallel_current/fixtures/diamond-example-inner-batch.loop
```

must emit `parallel for`, 32-sized tile expressions, and the diagonal expression `i4 + (-1 * i5)`. The diagonal expression is the useful witness: it shows that the output is not just rectangular tiling over `t` and `i`, but a skewed diamond schedule where one source index is reconstructed from coupled schedule coordinates.

The `diamond-current-jacobi-batch-codegen-gap` case records a narrower current limit. Batched two-statement Jacobi exposes an independent batch dimension, but the diamond route currently fails after validation during annotated parallel code generation:

```text
Annotated parallel codegen produced non-affine instruction trace loop
```

That failure is not evidence that the explicit batch dimension is semantically dependent. It is a code-generation guard for non-affine instruction traces after the diamond schedule has been lowered. The positive single-statement batch stencil and this negative Jacobi-batch case together document the current supported shape.
