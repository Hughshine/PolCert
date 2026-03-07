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
- succeeded: 45
- failed: 17

Current strict-path failing set:
- adi
- advect3d
- corcol
- corcol3
- covcol
- dct
- doitgen
- fusion1
- fusion8
- jacobi-1d-imper
- jacobi-2d-imper
- lu
- multi-stmt-stencil-seq
- pca
- ssymm
- tricky1
- trisolv

This directory intentionally reflects the strict proved runtime path: no CLI fallback exporter is used, and `polopt` now runs `PreparedOpt.Opt` directly.
