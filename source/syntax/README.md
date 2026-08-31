# Syntax Frontend (`polopt`)

This directory contains the textual loop-language frontend used by the `polopt` executable.

For a user-oriented overview of the optimizer itself, start with [../POLOPT.md](../POLOPT.md).
This file focuses on the surface language.

## Purpose

`polopt` is a user-facing entrypoint for the verified optimization core in [driver/PolOpt.v](../driver/PolOpt.v). It is intended to exercise the real proved pipeline on a structured loop fragment:

```text
.loop text
-> parser / elaborator
-> Loop IR
-> Extractor.extractor
-> StrengthenDomain.strengthen_pprog
-> scheduler' (Pluto + verified validation)
-> PrepareCodegen.prepare_codegen
-> CodeGen.codegen
-> verified cleanup passes
-> Loop IR
```

The parser/elaborator and pretty-printer are engineering layers. The verified core starts at the `Loop` IR.

## Surface Syntax

Top-level example:

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
- `if` guards built from affine `<=` / `==` tests combined with `&&`
- scalar and array assignments
- arithmetic using `+`, `-`, `*`, `/` in general RHS expressions
- pure calls in RHS expressions
- ternary expressions `cond ? e1 : e2` in RHS expressions
- float literals in RHS expressions

Still intentionally restricted in affine positions (bounds, guards, indexes):

- `||` and `!` are not accepted in affine guards
- affine positions currently accept only constants, variables, affine sums, and constant-multiplied subexpressions
- division is not accepted in affine bounds, guards, or indexes
- general calls in affine bounds / guards / indexes
- non-affine ternaries in affine bounds / guards / indexes

## Writing examples

Recommended workflow:

1. start from a small structured nest
2. keep bounds / guards / indexes affine
3. put calls and ternaries only in RHS expressions
4. run `./polopt your-example.loop`
5. inspect `--extract-only` or `--debug-scheduler` if needed

Good starter examples live in:

- [examples](./examples)
- [../tests/polopt-generated/inputs](../tests/polopt-generated/inputs)

## Current Status

This frontend now drives the strict proved runtime path:

- `SPolOpt.opt = PolOpt.Opt`
- no CLI fallback exporter is used
- the scheduler path is the same path used by the proved optimizer definition

The pretty-printer is now display-oriented only. Semantic cleanup is performed in Coq after code generation. In particular:

- affine expression/test simplification is done in [polygen/LoopCleanup.v](../polygen/LoopCleanup.v)
- singleton-loop elimination is done in [polygen/LoopSingletonCleanup.v](../polygen/LoopSingletonCleanup.v)

## Example commands

Emit optimized loop:

```sh
./polopt syntax/examples/matadd.loop
```

Dump the extracted source OpenScop only:

```sh
./polopt --extract-only syntax/examples/matadd.loop
```

Debug scheduler stages:

```sh
./polopt --debug-scheduler syntax/examples/matadd.loop
```

## Benchmark status

The generated regression suite is under [../tests/polopt-generated](../tests/polopt-generated).

Current strict proved-path status:

- total generated inputs: `62`
- succeeded: `62`
- changed: `59`
- unchanged: `3`
- nontrivially changed: `59`
- automatically detected tiled outputs: `39`

These are the same strict-suite numbers reported in [../README.md](../README.md)
and [../POLOPT.md](../POLOPT.md). The CI gate itself is driven by
`tests/polopt-generated/strict_suite_manifest.json`; the prose here is just the
current observed result on that manifest-gated corpus.
