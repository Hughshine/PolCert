# polopt generated loop suite

This directory contains the generated `.loop` suite and per-case strict `polopt` results.

Layout:
- `inputs/`: generated `.loop` inputs, one file per Pluto benchmark case
- `cases/<name>/`: strict-path `polopt` result for one case

Per-case files:
- `input.loop`: the generated source input
- `input.pretty.loop`: normalized pretty-printed input, when optimization succeeded
- `optimized.loop`: optimized output loop, when optimization succeeded
- `diff.patch`: unified diff between normalized input and optimized output, when optimization succeeded
- `status.txt`: exit code and result metadata
- `stderr.txt`: failure diagnostics when optimization failed

Current benchmark split:
- total benchmark cases seen by the generator: `62`
- semantics-preserving generated `.loop` inputs: `62`
- explicitly unsupported and skipped: `0`

Current strict-path status:
- total inputs: `62`
- succeeded: `62`
- failed: `0`

Current successful-but-unchanged set:
- `1dloop-invar`
- `dsyr2k`
- `dsyrk`
- `floyd`
- `nodep`
- `noloop`
- `strmm`
- `tmm`
- `tricky4`
- `wavefront`

This directory intentionally reflects the strict proved runtime path:
- no CLI fallback exporter is used
- `polopt` runs `PreparedOpt.Opt` directly

Important generator policy:
- `.loop` generation must preserve source semantics
- `/=` is lowered to `x = x / y`
- `/`, pure calls, ternaries, and float literals are preserved rather than approximated
