# Feature Status

This note is the short answer to "what is currently user-facing, what is
proved, and what interface does it use?"

## `polopt`

### Default mode

Command:

```sh
./polopt file.loop
```

Status:

- theorem-aligned verified optimizer route
- affine scheduling + checked tiling
- no ISS by default

Proof object:

- optimizer: `Opt`
- theorem: `Opt_correct`

### Optional ISS mode

Command:

```sh
./polopt --iss file.loop
```

Status:

- theorem-aligned verified optimizer route
- ISS + affine scheduling + checked tiling

Proof object:

- optimizer: `Opt_with_iss`
- theorem: `Opt_with_iss_correct`

### ISS-only split checking

Command:

```sh
./polopt --iss --identity file.loop
```

Status:

- checked ISS split path
- useful for examining ISS itself without later scheduling

This route is centered on the verified ISS structural validator rather than the
default end-to-end optimizer theorem.

### Experimental parallel modes

Commands:

```sh
./polopt --parallel file.loop
./polopt --parallel --parallel-strict file.loop
./polopt --parallel-current 0 file.loop
```

Status:

- CLI-exposed
- backed by verified parallel certification / code generation components
- still experimental
- not the default theorem-aligned optimizer path

Relevant components:

- `src/ParallelValidator.v`
- `src/ParallelCodegen.v`
- `driver/ParallelPolOpt.v`

## `polcert`

### OpenScop validation modes

Commands:

```sh
./polcert before.scop after.scop
./polcert --kind tiling mid.scop after.scop
./polcert before.scop mid.scop after.scop
```

Status:

- affine validation uses OpenScop
- tiling validation uses OpenScop
- phase-aligned affine+tiling validation is supported

### ISS validation modes

Commands:

```sh
./polcert --iss-bridge bridge.txt
./polcert --iss-debug-dumps before.txt after.txt
```

Status:

- ISS is not currently validated through OpenScop
- ISS uses Pluto-derived bridge / debug-dump inputs
- this matches the fact that Pluto ISS operates on its internal program form,
  not on the old OpenScop-only path

## CI coverage

Main workflow:

- `.github/workflows/ci.yml`
- builds the repository Docker image
- runs `tools/ci/run_ci.sh`

`run_ci.sh` currently includes:

- proof build
- `check-admitted`
- extraction
- `polcert` / `polopt` builds
- `make test`
- `make test-iss-pluto-suite`
- `make test-iss-pluto-live-suite`
- `make test-polopt-loop-suite`

Additional workflow:

- `.github/workflows/full-tiling-suite.yml`
- runs the strict `polopt` loop suite plus both ISS suites

## Interface summary

- affine / tiling validation: OpenScop
- ISS validation: Pluto bridge / debug-dump inputs
- parallel route: `polopt` CLI only, not `polcert`
