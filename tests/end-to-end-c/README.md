# end-to-end C harness

This directory complements the strict `.loop -> .loop` regression suite with a
small whole-C harness workflow.

The purpose is to test a more realistic source-to-source story:

```text
C wrapper
-> loop fragment
-> theorem-aligned polopt route
-> optimized loop
-> transpile/splice back into C
-> compile and run
```

The correctness slice covers ordinary tiling, an ISS route, positive and
negative literal strides, native constant unrolling, checked unroll-jam, and
constant unrolling inside a parallel loop. Targeted matmul runs additionally
exercise explicit parallel and innermost vector output. Heavier `*_perf`
siblings remain performance-only.

The one-repeat correctness target is part of default CI. It checks both the
declared structural effects and executable equality against the source loop;
it does not make a performance claim.

Effect coverage is deliberately explicit. The handwritten cases require
observable markers for ordinary tiling, parallel/vector annotations,
constant unrolling, checked block unroll-jam, and stride normalization. The
ISS case checks route acceptance plus executable equality; the dedicated ISS
suites separately check that valid split witnesses are accepted and mutated
witnesses are rejected. Diamond effects and validation phases are checked by
the dedicated diamond suite because the auxiliary C lowering does not yet
implement the verified integer division semantics for negative operands.

For the broader generated whole-C campaign over the 62-case regression corpus,
see [../end-to-end-generated](../end-to-end-generated). That path synthesizes a
complete C harness from each `input.loop` / `optimized.loop` pair instead of
relying on handwritten wrappers.

## Layout

- `cases/<name>/meta.json`
  - points to the source `.loop`
  - records the `polopt` flags for the case
- `cases/<name>/wrapper.c.in`
  - C wrapper template with `/* POLCERT_KERNEL */` splice marker

Untracked generated output goes to:

- `out/<name>/`

## Run

Build `polopt`, then run:

```bash
opam exec -- make test-end-to-end-c-smoke
```

The CI-equivalent correctness target uses four requested OpenMP threads for
parallel cases and adds targeted parallel/vector matmul checks:

```bash
opam exec -- make test-end-to-end-c-correctness
```

For the heavier perf-oriented pair, run:

```bash
opam exec -- make test-end-to-end-c-perf
```

For a targeted checked vectorization smoke test, run:

```bash
opam exec -- make test-end-to-end-c-matmul-vector
```

For the generated 62-case suite, first materialize the `polopt` outputs and
then run:

```bash
opam exec -- make test-end-to-end-generated
```

Or run a single case manually:

```bash
python3 tools/end_to_end_c/run_case.py tests/end-to-end-c/cases/matmul --polopt ./polopt
```

## Current boundary

This harness currently compares:

- baseline wrapper + transpiled input `.loop`
- optimized wrapper + transpiled `polopt` output

Both sides share the same auxiliary `.loop`-to-C lowering. The executable
comparison therefore detects optimizer regressions; it is not an independent
verification of that lowering.

It does not yet compare against a Pluto-generated full C output. That is the
next natural extension once the basic splice workflow is stable.

It now records both:

- exact stdout equality
- numeric drift summaries (`max_abs_diff`, `max_rel_diff`)
- whether optimized output contains `parallel for` or `vector for`

So if a future case uses tolerances, the numeric difference is still reported
instead of being silently hidden.

Cases containing either `parallel for` or `vector for` are compiled with OpenMP
enabled before comparing the baseline and optimized executables. `vector for`
lowers to `#pragma omp simd`.

`--timeout-seconds` covers both the `polopt` invocation and the compiled
baseline / optimized executables, so a hung test binary now fails the case
instead of wedging the suite.

## Generated suite boundary

The generated suite under `tests/polopt-generated/cases/*` does not reuse the
original benchmark C sources. Some of those sources are whole programs, but
others are only `#pragma scop` fragments. To cover the entire generated corpus,
the suite instead:

- parses each `.loop`
- synthesizes declarations and deterministic initialization
- emits a checksum-based whole-program summary
- compares baseline and optimized executables on that synthesized wrapper

This makes it possible to cover the full generated corpus with a uniform
end-to-end benchmark path, at the cost of using generated wrappers rather than
the original benchmark driver code. The generated summary uses index-weighted
checksums to expose value permutations, but a checksum is not a proof of
element-wise memory equality. CI uses fixed deterministic parameters and does
not currently add randomized dimensions or sanitizer instrumentation.
