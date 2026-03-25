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

These cases are not yet in default CI. They are a strengthening track for the
artifact rather than part of the minimal regression gate.

For the broader generated whole-C campaign over the 62-case regression corpus,
see [../end-to-end-generated](../end-to-end-generated).

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

Or run a single case manually:

```bash
python3 tools/end_to_end_c/run_case.py tests/end-to-end-c/cases/matmul --polopt ./polopt
```

The larger generated perf refresh is:

```bash
opam exec -- make test-end-to-end-generated-perf-refresh
```

## Current boundary

This harness currently compares:

- baseline wrapper + transpiled input `.loop`
- optimized wrapper + transpiled `polopt` output

It does not yet compare against a Pluto-generated full C output. That is the
next natural extension once the basic splice workflow is stable.
