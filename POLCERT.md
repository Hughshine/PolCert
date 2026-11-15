# Standalone Validation with polcert

`polcert` checks supplied polyhedral models without running the complete
loop-to-loop compiler. It uses the affine and tiling validators also used by
`polopt`. Build instructions are in [Environment](ENVIRONMENT.md).

## Affine Scheduling

```sh
./polcert before.scop after.scop
./polcert --require equiv before.scop after.scop
```

Supply two OpenScop models with the supported common domains and accesses.
The checker tests refinement in both directions and reports `[EQ]` when each
schedule refines the other, `[GT]` when `after.scop` refines `before.scop`,
`[LT]` for the converse, and `[NE]` otherwise. `--require` selects the result
that exits with status 0:

| `--require` | Exit status 0 for |
| --- | --- |
| `refines` (default) | `[GT]` or `[EQ]`: `after.scop` refines `before.scop` |
| `equiv` | `[EQ]` |
| `refined-by` | `[LT]` or `[EQ]`: `before.scop` refines `after.scop` |

`refines` is the target-to-source (backward simulation) direction that
translation validation and `polopt` check: every execution of `after.scop` is
matched by an execution of `before.scop` with an equivalent result. `equiv`
is mainly useful in this affine two-input mode: tiling and the multi-file
forms below support only `refines`. Without `--affine`, a pair related in
neither direction is checked as a tiling pair.

The checker omits instruction bodies and relies on the supplied access
summaries and memory model. Acceptance is consequently a model-level result,
not a proof of arbitrary C-program equivalence.

## Tiling and Phase Composition

```sh
./polcert --kind tiling mid.scop posttile.scop
./polcert before.scop mid.scop posttile.scop
./polcert before.scop mid.scop posttile.scop after.scop
```

The three-file form checks affine scheduling followed by tiling. The four-file
form adds post-tiling affine validation. Add `--second-level-tile` for the
corresponding two-level layout. These files must represent actual consecutive
stage results; [Pluto interface](doc/PLUTO_INTERFACE.md) explains the exports.

A runnable positive control is:

```sh
./polcert --kind tiling \
  tools/tiling_routes/fixtures/diamond-tile-example.midtransform.scop \
  tools/tiling_routes/fixtures/diamond-tile-example.posttile.scop
```

Expect acceptance through `permutable-band`. Failed recognition, failed band
conditions, or solver alarms do not certify a proposal. Tiling has no fallback
to general affine validation.

## Index-Set Splitting

```sh
./polcert --iss-bridge bridge.txt
./polcert --iss-debug-dumps before.txt after.txt
```

These modes check imported partition structure. The
[ISS fixtures](tests/iss-pluto-dumps/README.md) describe the input formats and
positive/negative expectations. Use `polopt --iss` when the desired result is
a compiled loop with an end-to-end refinement theorem.

## Interpreting Results

Check both the exit status and diagnostic. Rejection can mean an illegal
proposal, a conservative dependence check, or unsupported input structure.
A solver alarm is a failure to certify, not evidence that the transformation
is safe. Successful standalone checks do not perform extraction or code
generation and cannot establish their guarantees.

For compiler-stage contracts and the concrete instruction model, read
[Verified Pipeline](doc/VERIFIED_PIPELINE.md).
