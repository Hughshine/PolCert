# polopt generated loop suite

This directory contains the generated `.loop` suite and per-case strict `polopt` results.

For the user-facing optimizer story, see [../../POLOPT.md](../../POLOPT.md).
This file explains how to inspect the generated regression artifacts.

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

How to inspect a case:

1. read `input.loop`
2. compare with `optimized.loop`
3. scan `diff.patch` for the actual structural change
4. use `status.txt` to see whether the case changed or was left unchanged

Good cases to inspect first:
- `covcol`: statement splitting + reordered accumulation
- `intratileopt1`: clear loop interchange
- `costfunc`: skewing / wavefront-style reordering
- `matmul`: loop-order change on a familiar kernel

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
- `polopt` runs `CoreOpt.Opt` directly, i.e. the final `Opt` from `driver/PolOpt.v`

Important generator policy:
- `.loop` generation must preserve source semantics
- `/=` is lowered to `x = x / y`
- `/`, pure calls, ternaries, and float literals are preserved rather than approximated

Proof boundary:
- The strict suite runs the proved optimizer path from `driver/PolOpt.v` (`Opt = Opt_prepared`).
- The textual `.loop` parser/elaborator and the final pretty-printer are not part of the Coq theorem.
- The verified post-codegen cleanup passes are inside the proved path.
