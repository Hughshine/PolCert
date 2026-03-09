# polopt

`polopt` is the loop-language optimizer frontend backed by the verified optimization core.
It is the closest thing in this repository to a Pluto counterpart: Pluto is still used as the untrusted scheduler, but extraction, schedule validation, schedule/domain strengthening, code generation, and post-codegen cleanup are all tied to Coq proofs.

## Pipeline

The runtime pipeline is:

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

The final optimizer definition and theorem are in [driver/PolOpt.v](./driver/PolOpt.v):

- final optimizer: `Opt = Opt_prepared`
- final theorem: `Opt_correct`

The proved passes used by `Opt` are:

1. [src/Extractor.v](./src/Extractor.v)
   - `Extractor.extractor`
   - verified `Loop -> PolyLang` extraction
2. [src/StrengthenDomain.v](./src/StrengthenDomain.v)
   - `strengthen_pprog`
   - conservative strengthening of statement domains by implied parameter guards
3. [driver/PolOpt.v](./driver/PolOpt.v)
   - `scheduler'`
   - external scheduler wrapped by the verified validator
4. [src/PrepareCodegen.v](./src/PrepareCodegen.v)
   - `prepare_codegen`
   - reconciles explicit-depth semantics with the codegen-ready representation
5. [polygen/CodeGen.v](./polygen/CodeGen.v)
   - verified polyhedral code generation
6. verified post-codegen cleanup passes:
   - [polygen/LoopCleanup.v](./polygen/LoopCleanup.v)
   - [polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v)

## What is proved

The core theorem is `Opt_correct` in [driver/PolOpt.v](./driver/PolOpt.v).
At a high level, it states:

- if `polopt`'s verified core returns an optimized loop
- and the optimized loop runs to a final state
- then the original input loop can also run to an equivalent final state

This proof covers the optimizer core from `Loop` IR to optimized `Loop` IR.

## What is not proved

The following remain engineering layers around the proved core:

- the textual `.loop` parser / elaborator
- OpenScop textual parsing / printing implementation details
- Pluto itself
- the final OCaml pretty-printer

## Input language

`polopt` reads the structured `.loop` syntax documented in [syntax/README.md](./syntax/README.md).
This frontend is intentionally smaller than C. It is designed to give the verified core a clean structured loop fragment.

Supported in the current syntax frontend:

- symbolic parameters via `context(...)`
- structured `for` loops with half-open bounds
- affine `if` guards
- scalar and array assignments
- arithmetic using `+`, `-`, `*`, `/`
- pure calls in RHS expressions
- ternary expressions in RHS expressions
- float literals in RHS expressions

Still restricted in affine positions (bounds, guards, indexes):

- non-affine multiplication
- general calls in affine bounds / guards / indexes
- non-affine ternaries in affine bounds / guards / indexes

## Assumptions / model boundary

For the syntax-oriented frontend, `polopt` currently works over the lightweight `SInstr` model rather than full CompCert C semantics.
That means:

- calls are treated as pure computations
- the frontend does not model realistic floating-point rounding/precision effects
- the verified core still assumes the instruction-level non-aliasing / compatibility conditions required by the instantiated `Instr`
- practical C-level issues such as overflow, aliasing, and full floating-point semantics remain separate integration work

So the current `polopt` result should be read as:

- verified extraction / validation / code generation over the current loop-language model
- Pluto used as the untrusted scheduler inside that model

## Benchmarks and effect

The generated strict regression suite is under [tests/polopt-generated](./tests/polopt-generated).
Current strict proved-path status:

- total inputs: `62`
- succeeded: `62`
- changed: `52`
- unchanged: `10`

Interpretation:

- scheduling decisions come from Pluto itself
- the validated `polopt` path now accepts the same benchmark family across the suite
- the observed transformed loops therefore reflect Pluto's optimization choices, checked by the verified validator and completed by verified code generation / cleanup

One practical exception is performance on `advect3d`:

- it succeeds semantically
- but `CodeGen.codegen` currently takes about `40s` on that case
- the slowdown is in code generation, not in parsing, Pluto, or validation

## How to run

Build with the standard sequence from [README.md](./README.md), then run:

```sh
./polopt file.loop
```

Useful modes:

```sh
./polopt --extract-only file.loop
./polopt --debug-scheduler file.loop
```

## How to test

Full regression is already wired into CI through [tools/ci/run_ci.sh](./tools/ci/run_ci.sh).
Locally, the main commands are:

```sh
make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
make test
python3 tests/polopt-generated/tools/materialize_polopt_cases.py --timeout-seconds 120
```

The generated per-case results live under:

- [tests/polopt-generated/cases](./tests/polopt-generated/cases)

## Key source files

Compiler / CLI entry:
- [syntax/SLoopMain.ml](./syntax/SLoopMain.ml)

Frontend bridge to the verified optimizer:
- [syntax/SPolOpt.v](./syntax/SPolOpt.v)

Final optimizer definition and theorem:
- [driver/PolOpt.v](./driver/PolOpt.v)

Key passes:
- [src/Extractor.v](./src/Extractor.v)
- [src/StrengthenDomain.v](./src/StrengthenDomain.v)
- [src/PrepareCodegen.v](./src/PrepareCodegen.v)
- [polygen/CodeGen.v](./polygen/CodeGen.v)
- [polygen/LoopCleanup.v](./polygen/LoopCleanup.v)
- [polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v)
