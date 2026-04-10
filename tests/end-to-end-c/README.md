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

The current first slice is intentionally small:

- one ordinary tiled case: `matmul`
- one ISS-positive case: `reverse_iss`
- heavier perf-oriented siblings: `matmul_perf`, `reverse_iss_perf`

These cases are not yet in default CI. They are a strengthening track for the
artifact rather than part of the minimal regression gate.

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

For the heavier perf-oriented pair, run:

```bash
opam exec -- make test-end-to-end-c-perf
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

It does not yet compare against a Pluto-generated full C output. That is the
next natural extension once the basic splice workflow is stable.

It now records both:

- exact stdout equality
- numeric drift summaries (`max_abs_diff`, `max_rel_diff`)

So if a future case uses tolerances, the numeric difference is still reported
instead of being silently hidden.

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
the original benchmark driver code.
