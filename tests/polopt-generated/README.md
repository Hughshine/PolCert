# polopt generated loop suite

This directory contains the generated `.loop` inputs used to regression-test the
final proved `polopt` pipeline, including the verified affine stage and the
verified tiling stage with fallback to affine when tiling is unavailable.

Tracked content:
- `inputs/`: generated `.loop` inputs, one file per Pluto benchmark case
- `tools/`: scripts for materializing and checking per-case outputs
- `cases/<name>/`: checked materialized outputs produced by `polopt`

Run the full suite locally:

```bash
opam exec -- make test-polopt-loop-suite
```

That target:
1. builds the final `polopt`
2. runs it on all `62` generated inputs
3. materializes `tests/polopt-generated/cases`
4. loads `tests/polopt-generated/strict_suite_manifest.json` and checks:
   - all `62` cases succeed
   - at least `50` cases change structurally
   - at least `50` cases change nontrivially after ignoring alpha-renaming
     of loop variables and whole-program outer guard wrappers
   - the checker reports the automatically detected tiled cases
   - representative cases such as `matmul`, `matmul-init`, and `wavefront`
     are required to satisfy the tiling heuristic

If you only need the materialized `cases/<name>/` outputs for downstream
generated whole-C harnesses, without rerunning the strict checker gate, use:

```bash
opam exec -- make materialize-polopt-loop-suite
```

Current reporting:
- `changed` means the optimized pretty-printed loop differs from the input.
- `nontrivial_changed` means the loop still differs after:
  - alpha-normalizing loop induction variable names, and
  - stripping whole-program outer `if (...) { ... }` wrappers
- `detected_tiled_cases` means the optimized loop both:
  - increases the loop nesting depth by at least `2`, and
  - contains explicit tiled strip-mining markers (`max/min` bounds and `/ 32`)

How to inspect one case:

1. read `input.loop`
2. compare with `optimized.loop`
3. inspect `diff.patch`
4. read `status.txt`

Important proof boundary:
- The suite runs the final proved optimizer path from `driver/PolOpt.v`.
- The textual `.loop` parser/elaborator and final pretty-printer are outside
  the Coq theorem.
- The affine validator, checked tiling validator, `current_view_pprog`, and
  verified codegen path are inside the proved runtime pipeline.
