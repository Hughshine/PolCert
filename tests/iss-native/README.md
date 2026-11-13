# Native ISS fixtures

`reverse_rows.loop` and `reverse_columns.loop` are local matrix extensions of
Pluto's `reverse-iss` example. The one-dimensional source is under
`tests/end-to-end-c/cases/reverse_iss/`. `run_native_iss_suite.py` checks the
three inputs under five configurations; configurations are not extra kernels.

## Periodic Jacobi

The periodic fixtures adapt the computation regions of Pluto's
`test/jacobi-1d-periodic.c` and `test/jacobi-2d-periodic.c`. They retain the two
physical buffers, periodic boundary accesses, update multiplicities, and time
order. They do not replace alternating buffers with full-time storage.

The `phase` inputs express time as `t = 2*q + p + 1`, where `p` is zero or one.
The guard `t < T` removes the final unused phase. Thus the destination buffer
is `1-p`, and the source buffer is `p`; all access indices are affine. Pluto
actually splits this phase coordinate, and the generated loops separate the
two buffer-update phases. These are genuine ISS proposals, but not the spatial
midpoint cuts chosen by PET for the original C representation.

Two alternative one-dimensional representations are retained for diagnosis:

- `guards` spells out the boundary cases as separate statements. In the tested
  configuration, Pluto cuts at `-p-1=0` although `p` is zero or one. Each
  statement therefore gains an empty piece, without separating its nonempty
  phase regions. This representation is not counted as producing that effect.
- `quotient` represents `t % 2` by an additional bounded quotient iterator.
  Pluto does not split it in the tested native configuration.

These alternatives are not additional benchmarks.

## Evaluation Inputs from Pluto's ISS Tests

The `iss-supplement` evaluation cohort uses the following inputs in addition
to the reverse fixtures. Each is a computation from Pluto's `test/`
directory on which Pluto's `--iss` performs a split.

| Fixture | Pluto source | Representation |
| --- | --- | --- |
| `jacobi_1d_periodic_phase.loop` | `jacobi-1d-periodic.c` | phase form, `t = 2*q + p + 1` |
| `jacobi_2d_periodic_phase.loop` | `jacobi-2d-periodic.c` | phase form, `t = 2*q + p + 1` |
| `jacobi_1d_periodic_even_phase.loop` | `jacobi-1d-periodic-even.c` | phase form, `t = 2*q + p + 1`, extent `2*N` |
| `jacobi_3d_periodic_phase.loop` | `jacobi-3d-periodic.c` | phase form, `t = 2*q + p + 1` |
| `heat_2dp_phase.loop` | `heat-2dp.c` | phase form, `t = 2*q + p` (the source loop starts at `t = 0`) |
| `multi_stmt_periodic_phase.loop` | `multi-stmt-periodic.c` | phase form, `t = 2*q + p + 1`, two statements |
| `multi_stmt_2d_periodic_phase.loop` | `multi-stmt-2d-periodic.c` | phase form, `t = 2*q + p + 1`, two statements |
| `bidirec_2d.loop` | `2d-bidirec.c` | direct conversion |

The phase inputs follow the convention above: conditional subscripts become
conditional reads, and `p` selects the source buffer. On this representation
Pluto cuts the phase coordinate; on the original C it cuts spatial midpoints.
The evaluation's ISS review (`evaluation/bin/review_paired_iss.py`) checks
the phase inputs with `phase_harness` in `tools/iss/run_periodic_iss_suite.py`:
bitwise-equal buffers, equal writes per cell, and one physical buffer per
final assignment site, on samples that include empty and singleton domains
and tile boundaries.

`bidirec_2d.loop` is split by Pluto (cut `2j-N = 0`), and the split is
accepted by PolCert's ISS check. Pluto then aborts when it re-reads the split
program for scheduling (an assertion in its isl dependence extraction), so
PolCert exits with status 2 and the evaluation records `native-failed` for all
five configurations. The independent baseline, a single Pluto run, succeeds.
Its review (`iss_review: source-values`, `value_harness` in
`tools/iss/run_periodic_iss_suite.py`) requires both outputs to reproduce the
source array bitwise, with the same writes per cell, for sizes from 0 to 97,
and to keep more assignment sites than the source.

`SInstr` conservatively includes reads from both branches of a conditional
expression in its access summary. The `phase` representation therefore has
the same executed physical accesses as the C computation, but a larger static
read summary than PET's piecewise accesses. No frontend semantics or proof is
changed by these fixtures.

## Checks

Run `tools/iss/run_periodic_iss_suite.py` against an already-built tree. It
captures actual Pluto inputs and ISS witnesses, checks that the split is
forwarded, and compiles a complete-execution observer for the original C
computation, adapted input, and final generated loop. The observer compares:

- every selected physical read and the version of the value read;
- the number of writes to each cell and both final buffers;
- separation of the two nonempty phase regions at final assignment sites.

The one-dimensional suite uses 114 parameter pairs; the two-dimensional suite
uses 98. Both include empty and singleton domains, tile boundaries, and multiple
buffer reuses. Large-time samples use zero initial values to avoid machine
overflow; their access-version checks remain active. These are complete
executions at bounded parameter values, not an exhaustive correctness proof.

`test_periodic_iss_harness.py` checks the observer itself against wrong-buffer,
wrong-boundary, missing-update, duplicate-execution, and wrong-diagonal mutations.
`run_phase_iss_adapter_tests.py` separately checks candidate reconstruction and
the unchanged extracted complete-cut checker, including invalid partitions and
instruction/access payload changes.
