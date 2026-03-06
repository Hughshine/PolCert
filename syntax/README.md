# Syntax Frontend Experiment

This directory isolates a lightweight frontend for `SPolOpt`.
It does not reuse `Convert.v` and does not touch the existing validator driver.

## Purpose

The goal is to exercise the real `Loop -> extractor -> scheduler/validator -> codegen -> Loop`
pipeline with a syntax-oriented instruction language (`SInstr`) whose dynamic semantics stay trivial,
but whose structural interface (`waccess`, `raccess`, `to_openscop`) is real.

## Surface Syntax

Top-level:

```text
context(N, M);
for i in range(0, N) {
  for j in range(0, M) {
    C[i][j] = A[i][j] + B[i][j];
  }
}
```

Supported constructs:

- `context(x, y, ...)` for symbolic parameters
- `for i in range(lb, ub) { ... }` with half-open bounds `[lb, ub)`
- `if (a <= b && c == d) { ... }`
- scalar and array assignments
- affine arithmetic using `+`, `-`, `*` by integer constants

Deliberately unsupported for now:

- `else`
- `||`, `!`
- division/mod/max/min in source syntax
- non-affine multiplication

## Current Status

- `polopt --extract-only <file.loop>` is working and emits raw OpenScop on stdout.
- The extracted OpenScop is accepted by the existing `polcert` validator when read back as a `.scop`.
- The default `polopt <file.loop>` currently stops inside Pluto scheduling. Pluto reports
  `isl_map.c:12117: number of columns too small`, and the extracted runtime reports
  `Scheduler validation failed`.

This points to a scheduler/OpenScop compatibility gap, not a frontend parse/elaboration failure.
The most visible difference from Pluto-generated `.scop` files is that the current generic
`PolyLang.to_openscop` emits a compact scattering relation and fewer domain/context guards.

## Elaboration Convention

The frontend elaborates source names to the actual `Loop` environment order used by the Coq semantics:

- innermost iterator is `Var 0`
- then outer iterators
- then top-level context parameters

Instruction slots are emitted as the identity list `[Var 0; Var 1; ...]` at parse time.
The pretty-printer for optimized output does not ignore these slots; it substitutes them back through
`Loop.Instr instr es`, so optimized schedules still print meaningfully.
