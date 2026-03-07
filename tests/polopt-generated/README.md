# polopt generated loop suite

This directory contains the generated `.loop` suite and per-case strict `polopt` results.

Layout:
- `inputs/`: generated `.loop` inputs, one file per Pluto benchmark case.
- `cases/<name>/`: strict-path `polopt` result for one case.

Per-case files:
- `input.loop`: the generated source input.
- `input.pretty.loop`: normalized pretty-printed input, when optimization succeeded.
- `optimized.loop`: optimized output loop, when optimization succeeded.
- `diff.patch`: unified diff between normalized input and optimized output, when optimization succeeded.
- `status.txt`: exit code and result metadata.
- `stderr.txt`: failure diagnostics when optimization failed.

Current strict-path status:
- total: 62
- succeeded: 55
- failed: 7

Current strict-path failing set:
- advect3d
- corcol3
- fusion1
- jacobi-1d-imper
- jacobi-2d-imper
- lu
- multi-stmt-stencil-seq

This directory intentionally reflects the strict proved runtime path: no CLI fallback exporter is used.
