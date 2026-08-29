# Draft: Silent Miscompilations in Pluto

Status: draft for upstream issue reports

Last checked: 2026-08-28

Audience: Pluto maintainers

This document describes four independent Pluto transformations that silently
produce wrong C programs. Each issue has a minimized executable witness. The
four defects still reproduce on the latest official `bondhugula/pluto`
`master` checked on 2026-08-28. A fifth issue affected the `verif-scop/pluto`
fork used during PolCert development; official Pluto did not contain that
regression. The fix is on the fork's
`fix/diamond-reschedule-with-nointratileopt` branch and has not been merged into
the fork's `master` branch.

The reports should be filed as separate upstream issues. They exercise
different transformations and require independent fixes and regression tests.

## Version Matrix

| Repository | Revision | Evidence | Result |
|---|---|---|---|
| `bondhugula/pluto` | `dc462163c8b4fc97d378a4d245d1a64741cb4111` (`master`, 2026-05-06) | Built and executed on 2026-08-28 | The forced affine order, vanished parallel coordinate, no-tile unroll-jam, and inner-parallel tiling cases still miscompile. Pure diamond and full-diamond variants produce the expected result. |
| `verif-scop/pluto` | `6f43860b6c4cddeeca09189bf3073f05b78b14a5` (`master`, 2026-05-05) | Source re-audit on 2026-08-28 | The four unresolved code paths are present. This fork also contains the conditional diamond-restore regression described below. |
| `verif-scop/pluto` | `56b66690edeed1ef17ddc018bbf67666795a3fd4` (`fix/diamond-reschedule-with-nointratileopt`) | Built and executed on 2026-08-28 | The diamond regression is fixed on this branch. The other four witnesses remain active PolCert regression tests. |

The official checkout does not support the fork's `--dumpscop` option. The
latest-version recheck therefore used raw `polycc` output for executable
comparisons and the fork only where a PolCert before/after phase dump was
needed.

## Result Summary

| ID | Transformation | Source result | Pluto result | Latest official status | PolCert outcome |
|---|---|---:|---:|---|---|
| P1 | User-forced affine statement grouping through `.fst` | `100` | `0` | Reproduced at `dc462163` | Affine validation rejects the schedule; the complete route emits no optimized loop. |
| P2 | Parallel annotation after a one-trip schedule coordinate vanishes | `10000` | `2499` in repeated four-thread runs | Reproduced at `dc462163` | Strict hint mapping and a direct check of the actual inner dimension both reject. |
| P3 | Unroll-jam under `--notile` | `15` | `1` | Reproduced at `dc462163` | Proved block unrolling is retained, but the unsafe local jam is rejected. |
| P4 | `--tile --parallel --innerpar` satisfaction metadata | `310235039` | `928116`, `7631020`, and `23122525` in three four-thread runs | Reproduced at `dc462163` | Rectangular tiling is accepted; the unsafe parallel overlay is removed or rejected in strict mode. |
| F1 | Diamond tiling without intra-tile optimization in the `verif-scop` phase-dump patch | `20` | `18`; full-diamond: `15` | Not present in official `dc462163`; fixed in fork commit `56b6669` | The mixed-scalar candidate is conservatively rejected; a separate supported pure-diamond case is accepted. |

Parallel wrong-code results can vary across executions. The values above are
observations from the 2026-08-28 recheck, not invariants of the defects.

## P1: `.fst` Can Force an Illegal Affine Statement Order

### Suggested issue title

`.fst` statement grouping can place a consumer before its producer

### Minimal witness

- C source: `tests/pluto-bugs/affine-fst-reversed/affine_fst_reversed.c`
- control file: `tests/pluto-bugs/affine-fst-reversed/reversed.fst`

Copy `reversed.fst` to `.fst` in the working directory, then run:

```sh
polycc --notile --nodiamond-tile --nointratileopt --noprevector \
  --nounrolljam --noparallel affine_fst_reversed.c
gcc -O2 affine_fst_reversed.c -o baseline
gcc -O2 affine_fst_reversed.pluto.c -o optimized
./baseline
./optimized
```

Expected behavior: Pluto should either reject the inconsistent grouping or
emit a program that prints `100`.

Observed behavior: Pluto exits successfully, emits the complete consumer loop
before the producer loop, and the generated program prints `0`.

### Root cause

`lib/pluto.c:873-940` reads `.fst` and installs scalar statement groups
directly. Dependence satisfaction is then updated incrementally. There is no
independent final check that the complete lexicographic schedule preserves all
dependences. A later positive loop coordinate can therefore mark a dependence
satisfied even though an earlier scalar coordinate is negative.

### Suggested fix and regression

Validate the final schedule against every dependence after applying `.fst` or
`.precut`. The validation must inspect the complete lexicographic schedule,
not only the dimension currently being constructed. Parser failures, missing
statement identifiers, duplicate identifiers, and an inconsistent grouping
should be fatal. The minimized source and `.fst` file should become an
executable negative regression.

### PolCert cross-check

PolCert's standalone affine checker rejects the Pluto before/after schedule.
The complete route keeps the source domains, accesses, and instructions,
imports only the candidate scattering, reports the failed validation, and
emits no optimized Loop program.

## P2: A Vanished Coordinate Can Transfer Parallelism to a Dependent Loop

### Suggested issue title

`Parallel AST fallback crosses the selected band when a loop vanishes`

### Minimal witness

- C source: `tests/pluto-bugs/vanished-outer-parallel/vanished_outer_parallel.c`

```sh
polycc --notile --nodiamond-tile --nointratileopt --noprevector \
  --nounrolljam --parallel vanished_outer_parallel.c
gcc -O2 vanished_outer_parallel.c -o baseline
gcc -O2 -fopenmp vanished_outer_parallel.pluto.c -o optimized
./baseline
OMP_NUM_THREADS=4 ./optimized
```

Expected behavior: the dependent inner recurrence remains sequential and both
programs print `10000`.

Observed behavior: CLooG removes the one-trip outer coordinate, Pluto emits an
OpenMP pragma on the inner recurrence, and four-thread executions produce an
incorrect value. The latest-version recheck produced `2499` in three runs.

### Root cause

`tool/ast_transform.c:75-95` searches inward when the selected parallel loop
does not survive CLooG. Its boundary condition is:

```c
inloops[0]->depth > band->loop->depth + band->width
```

The band occupies the half-open depth interval
`[band->loop->depth, band->loop->depth + band->width)`. The condition therefore
allows the fallback to cross the boundary at equality and annotate a loop that
was not part of the selected parallel band.

### Suggested fix and regression

Changing `>` to `>=` closes the immediate off-by-one defect. A stronger fix is
to carry an exact mapping from the selected polyhedral schedule dimension to
the surviving CLAST loop and to decline the annotation when that dimension was
eliminated. The regression should use a one-trip independent outer loop and a
dependence-carrying inner loop, then execute the generated OpenMP program.

### PolCert cross-check

PolCert's strict route rejects the parallel hint because the selected
coordinate has no surviving certifiable loop. A separate test asks PolCert to
check the concrete inner coordinate chosen by Pluto's fallback; its dependence
check also rejects that loop.

## P3: No-Tile Unroll-Jam Can Cross a Non-Permutable Loop

### Suggested issue title

`--notile --unrolljam assumes one tiled level and jams across a dependence`

### Minimal witness

- C source: `tests/pluto-bugs/notile-unrolljam-nonpermutable/notile_unrolljam_nonpermutable.c`

```sh
polycc --identity --notile --nodiamond-tile --nointratileopt \
  --noprevector --unrolljam --ufactor=2 --noparallel \
  notile_unrolljam_nonpermutable.c
gcc -O2 notile_unrolljam_nonpermutable.c -o baseline
gcc -O2 notile_unrolljam_nonpermutable.pluto.c -o optimized
./baseline
./optimized
```

Expected behavior: both programs print `15`.

Observed behavior: Pluto places the statements for `j` and `j+1` adjacent
inside the `k` loop. The second statement reads the value for `k=3` before the
first statement has produced it. The generated program prints `1`.

### Root cause

`lib/polyloop.c:575-605` calls:

```c
pluto_get_innermost_permutable_bands(prog, 1, &num_ibands)
```

The hard-coded second argument assumes that one tiled loop level exists. Under
`--notile`, candidate discovery skips the actual permutable-band boundary and
admits the dependence-carrying `j` loop. The later AST rewrite applies the jam
without independently validating that local permutation.

### Suggested fix and regression

Pass the number of tiled levels actually introduced by the selected pipeline;
it is zero under `--notile`. Independently validate each proposed jam
permutation immediately before the AST rewrite. The executable regression
should retain the dependence that becomes visible only after the unsafe jam.

### PolCert cross-check

PolCert implements the transformation as proved block unrolling followed by a
local trace-permutability check. It emits the unrolled blocks but preserves
separate `k` loops when the jam proof fails, so the generated program remains
equivalent to the source.

## P4: `--innerpar` Moves Satisfaction Bits Without the Matching Schedule

### Suggested issue title

`--tile --parallel --innerpar can mark a dependence-carrying tile loop parallel`

### Minimal witness

- C source: `tests/pluto-bugs/tiling-innerpar-satvec/tiling_innerpar_satvec.c`
- tile sizes: `tests/pluto-bugs/tiling-innerpar-satvec/tile.sizes`

Copy `tile.sizes` into the working directory, then run:

```sh
polycc --identity --tile --parallel --innerpar --nodiamond-tile \
  --nointratileopt --noprevector --nounrolljam tiling_innerpar_satvec.c
gcc -O2 tiling_innerpar_satvec.c -o baseline
gcc -O2 -fopenmp tiling_innerpar_satvec.pluto.c -o optimized
./baseline
OMP_NUM_THREADS=4 ./optimized
```

Expected behavior: the two-dimensional recurrence remains sequential and both
programs print `310235039`.

Observed behavior: Pluto emits `#pragma omp parallel for` on tile loop `t4`.
Three executions of the official latest revision printed `928116`, `7631020`,
and `23122525`.

### Root cause

`lib/tile.c:433-478` skips the wavefront schedule construction under
`--innerpar`, but still moves dependence-satisfaction bits from inner
dimensions to the outer tile-space dimension. Later parallel-loop discovery
trusts this metadata even though the actual schedule does not satisfy those
dependences at the tile-space dimension.

### Suggested fix and regression

Do not transfer satisfaction bits unless the transformation constructs the
schedule that justifies the transfer. Recompute directions and satisfaction
from the final schedule, and validate the exact loop selected for the OpenMP
annotation. The regression should execute a multi-tile two-dimensional
recurrence with several OpenMP threads.

### PolCert cross-check

PolCert validates rectangular tiling and parallelization as separate claims.
It accepts the legal permutable-band tiling, finds no parallel dimension, and
emits a sequential tiled program in non-strict mode. Strict parallel mode
rejects the candidate and emits no optimized program.

## F1: Fork-Specific Diamond Restore Regression

This issue should not be filed against official `bondhugula/pluto`. Official
revision `dc462163` calls `pluto_diamond_tile_reschedule` unconditionally and
produces `20` for both the partial- and full-diamond variants.

The phase-dump patch in `verif-scop/pluto` commit `7d6fae8` made that call
conditional on `options->intratileopt`; the regression remained present at the
audited predecessor `488ea2f`. The call restores a hyperplane temporarily
evicted during concurrent-start diamond schedule construction; it is required
for correct code generation and is distinct from the optional intra-tile
locality pass. With `--nointratileopt`, the affected partial-diamond program
printed `18` and the full-diamond program printed `15`, rather than `20`.

Fork commit `56b66690edeed1ef17ddc018bbf67666795a3fd4` on
`fix/diamond-reschedule-with-nointratileopt` restores the unconditional call
and adds an executable regression. The fixed branch and official latest both
print `20`; `verif-scop/master` does not yet contain this fix.

PolCert conservatively rejects the corresponding mixed-scalar candidate, but
that rejection does not diagnose the missing Pluto restore. A separate typed
`diamond-stencil` positive test demonstrates that PolCert accepts a supported
pure-diamond mapping through checked tiling, post-tiling affine validation, and
proved Loop code generation.

## Reproduction in the PolCert Artifact

The pinned-fork producers and their checked PolCert outcomes run with:

```sh
opam exec -- make test-pluto-bugs
```

The target checks more than process exit status. For every reproduced
miscompilation it compiles and executes the original and Pluto-generated C,
asserts the expected mismatch, then checks the corresponding PolCert behavior.
The fork-specific diamond regression asserts equality after the fix.

Official-latest confirmation used a separate build of
`bondhugula/pluto@dc462163c8b4fc97d378a4d245d1a64741cb4111`. The four raw producer
commands above omit the fork-only `--dumpscop` flag. The code paths identified
in the root-cause sections remain unchanged in that revision.

## What the PolCert Result Establishes

PolCert treats Pluto as an untrusted candidate generator. It does not prove
that Pluto is correct, and it does not accept Pluto's dependence-satisfaction
bits, parallel annotations, or generated C as certificates. Instead, it
checks each semantic boundary independently:

1. affine schedules must pass dependence-legality validation;
2. ISS candidates must carry a checked source-to-split witness;
3. ordinary, two-level, and diamond tiling must satisfy the corresponding
   checked tiling relation;
4. post-tiling affine schedules are revalidated;
5. parallel and innermost-vector annotations require a fresh check of the
   concrete loop dimension;
6. unroll-jam uses proved unrolling and validates the local jam permutation;
7. final Loop code is produced by PolCert's proved code generator.

These boundaries reject or remove the unsafe transformation in P1-P4. This is
evidence that the validation architecture blocks these concrete Pluto
failures. It is not a claim that PolCert can validate arbitrary Pluto-generated
C. SIMD instructions, scalar privatization, storage expansion, state-changing
transformations, and inputs outside PolCert's modeled IR remain outside this
claim.
