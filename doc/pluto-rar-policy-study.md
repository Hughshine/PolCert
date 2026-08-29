# Pluto RAR Policy: Source Audit and Checked A/B Study

Status: artifact engineering note, 2026-08-29

Audience: PolCert users and evaluators who need to interpret Pluto's `--rar`
flag, not just reproduce a command line.

## Short Answer

RAR means read-after-read, also called an input dependence. Two reads of the
same location do not impose a semantic execution order. Pluto can nevertheless
use their proximity as a reuse signal: when `--rar` is enabled, it computes
read-read relations and feeds them to the dependence-distance bounding part of
its scheduling objective. It does not use them as legality constraints.

The flag therefore changes which legal affine schedule Pluto prefers. It does
not authorize a transformation, establish that a loop is parallel, or replace
PolCert validation. A different affine schedule can later expose a different
permutable band, tiled loop order, parallel hint, or prevector hint, so the
observable effect can extend beyond the first scheduling phase.

PolOpt now follows Pluto's default and leaves RAR disabled unless the caller
supplies `--rar`. Historical tests that were calibrated with RAR retain an
explicit flag. Both policies use the same validators and verified code
generation.

## What the Pinned Pluto Source Does

This audit uses the ordinary artifact Pluto revision
`8c43c210c9c08c5958198f22db4b54000380925e`.

1. `pluto_options_alloc` initializes `options->rar` to zero. Pluto's own CLI
   documentation describes `--rar` as an optional optimization setting that is
   disabled by default.
2. `compute_deps_isl` computes RAR relations only when the flag is enabled. With
   the default dependence mode, the relation connects an earlier read to a later
   read of the same location. With `--lastwriter`, it instead uses the last read
   reaching the later read.
3. `compute_permutability_constraints_dep` explicitly omits RAR relations from
   permutability constraints. It still constructs their dependence-distance
   bounding constraints, unless dependence bounding is disabled.
4. Legality completion, satisfaction-vector construction, the dependence graph,
   parallel-loop detection, permutable-band discovery, and ordinary tile
   metadata ignore RAR. Pluto does still record oriented `satisfied` and
   `satisfaction_level` metadata for RAR; that state determines how long a
   read-read relation keeps contributing bounding constraints as hyperplanes
   are selected.

These observations describe the ordinary non-DFP route used by the A/B study.
Pluto's separate DFP implementation also uses RAR in pairwise constraints and
its skew/tile-prevention heuristic. That remains an optimization heuristic, not
a semantic ordering requirement, but it means that “tiling ignores RAR” would
be too broad a statement about every Pluto solver route.

The fixed source can be inspected in
[`lib/program.cpp`](https://github.com/verif-scop/pluto/blob/8c43c210c9c08c5958198f22db4b54000380925e/lib/program.cpp),
[`lib/framework.cpp`](https://github.com/verif-scop/pluto/blob/8c43c210c9c08c5958198f22db4b54000380925e/lib/framework.cpp),
[`lib/pluto.c`](https://github.com/verif-scop/pluto/blob/8c43c210c9c08c5958198f22db4b54000380925e/lib/pluto.c), and
[`lib/polyloop.c`](https://github.com/verif-scop/pluto/blob/8c43c210c9c08c5958198f22db4b54000380925e/lib/polyloop.c).

There is one implementation detail worth separating from the published model.
The PLDI 2008 formulation bounds the absolute transformed distance of an input
dependence, which requires upper and lower bounds. This pinned source constructs
only the oriented bound `phi(destination) - phi(source) <= u.p + w`; it does not
construct the reverse bound in `compute_permutability_constraints_dep`. The RAR
relation itself is oriented from an earlier read to a later read, or from the
last read under `--lastwriter`. Consequently, reversing such a pair in the new
schedule can satisfy the one-sided bound with a large negative distance. This
differs from absolute-proximity minimization and can weaken the intended reuse
heuristic, but it does not create a correctness obligation because RAR ordering
is semantically irrelevant.

## What the Pluto Literature Says

The papers discuss the concept directly, although they do not argue that the
current command-line flag should be enabled by default.

The CC 2008 transformation paper includes input (read-after-read) dependences in
its generalized dependence graph and interprets transformed dependence distance
as a measure of reuse distance or communication volume. It then minimizes a
parametric upper bound on that distance. This gives the historical motivation
for considering RAR during schedule selection: two reads that remain close in
the transformed order can reuse a cache line or tile-resident value. However,
that paper states its legality condition for every graph edge and assumes a
nonnegative transformed distance; it does not yet express Pluto's current
objective-only treatment of RAR. See
[Bondhugula et al., CC 2008](https://www.csa.iisc.ac.in/~udayb/publications/uday-cc08.pdf).

The PLDI 2008 Pluto system paper introduces the distinction used here. Section
4.1 states that RAR
ordering need not be preserved, omits legality constraints for input
dependences, and retains them only in the bounding objective, with distance
bounded in both directions. See
[Bondhugula et al., PLDI 2008](https://www.ece.lsu.edu/jxr/Publications-pdf/pldi08.pdf).
Its matrix-vector-transpose example also shows the intended tradeoff. The RAR
objective favors fusing an `ij` traversal with a permuted `ji` traversal so that
both statements read the same matrix element close together. That choice
improves matrix reuse but replaces independent parallel loops with pipelined
parallelism. RAR can therefore trade one useful schedule property for another.

Bondhugula's dissertation gives the clearest conceptual statement: RAR
relations are not actual data dependences, but they characterize reuse. Section
3.12 then makes the same legality-versus-objective distinction as the PLDI
paper. See
[Effective Automatic Parallelization and Locality Optimization Using the Polyhedral Model](https://www.csa.iisc.ac.in/~uday/publications/uday-thesis.pdf).

The practical reading is therefore:

- RAW, WAR, and WAW constrain which schedules preserve program behavior.
- RAR ranks otherwise legal schedules according to a read-reuse proxy.
- The proxy is analytical, not a cache simulator, so enabling RAR is a policy
  choice rather than a correctness improvement.

## Checked Corpus Comparison

`tools/artifact/compare_rar_policy.py` changes only the presence of `--rar` and
runs both candidates through PolOpt. The results below use the fixed Pluto
revision above and the 62 generated Loop fixtures. Times cover the complete
checked driver invocation, including validation and code generation, and come
from one run in the artifact container.

| Checked route | Comparable accepted pairs | Different final Loop programs | no-RAR total | RAR total | Aggregate ratio | Median per-case ratio |
|---|---:|---:|---:|---:|---:|---:|
| affine-only, sequential | 62 | 16 (25.8%) | 42.516 s | 45.135 s | 1.062x | 1.038x |
| affine plus tiling, sequential | 60 | 15 (25.0%) | 165.710 s | 172.026 s | 1.038x | 1.027x |

For the tiled comparison, `noloop` was rejected under both policies because it
contains no loop to tile. `advect3d` reached the 60-second limit under both
policies. Neither case indicates a policy-specific acceptance difference.

The affine-only programs that changed were `advect3d`, `corcol`, `covcol`,
`dct`, `dsyr2k`, `dsyrk`, `fusion4`, `gemver`, `intratileopt1`,
`intratileopt4`, `matmul`, `polynomial`, `ssymm`, `strmm`, `strsm`, and `tce`.
The tiled list is the same except for the timed-out `advect3d` case.

Five changed cases were also compared under checked parallel and vector routes:
`corcol`, `dct`, `dsyrk`, `matmul`, and `ssymm`. All five produced different
final Loop programs under both modes. The certified annotation effect was not
monotonic:

- `corcol` had a certified parallel loop without RAR and no certified parallel
  loop with RAR.
- `dsyrk` and `matmul` had no certified vector loop without RAR and did have one
  with RAR.

These are downstream effects of choosing a different affine schedule. RAR does
not itself prove or disprove parallelism or vectorizability.

## Executable Spot Checks

Two changed parallel routes were compiled and run at dimensions 768 with
`OMP_NUM_THREADS=4` in the environment. Each number is the best of 15 executions
in one container. Both optimized programs passed the output comparison at the
harness's default absolute and relative tolerances of `1e-9`.

| Case | Policy | Certified parallel loop | Baseline | Optimized | Speedup |
|---|---|---:|---:|---:|---:|
| `corcol` | no RAR | yes | 0.195691 s | 0.048055 s | 4.072x |
| `corcol` | RAR | no | 0.195942 s | 0.047924 s | 4.089x |
| `matmul` | no RAR | yes | 0.148790 s | 0.055679 s | 2.672x |
| `matmul` | RAR | yes | 0.148697 s | 0.037466 s | 3.969x |

The `corcol` result is an important warning against reading annotation counts as
performance. The recorded best times differ by about 0.27% even though only one
candidate carries a certified parallel loop; this measurement does not isolate
the cause of that similarity. For `matmul`, the RAR candidate is about 1.49
times faster in the recorded best times. This one result shows that the policy
can matter; it does not establish that RAR is generally faster.

## Reproduction

Build `polopt`, then run the structural comparisons:

```sh
python3 tools/artifact/compare_rar_policy.py \
  --pipeline affine --mode sequential \
  --output /tmp/rar-affine-sequential.json

python3 tools/artifact/compare_rar_policy.py \
  --pipeline tiled --mode sequential \
  --output /tmp/rar-tiled-sequential.json

python3 tools/artifact/compare_rar_policy.py \
  --pipeline tiled --mode parallel --mode vector \
  --only corcol,dct,dsyrk,matmul,ssymm \
  --output /tmp/rar-selected-par-vector.json
```

`make compare-rar-policy` runs the default tiled sequential comparison. The
checked results quoted above are retained as
[`rar_full_affine_sequential_report.json`](../tests/end-to-end-generated/rar_full_affine_sequential_report.json),
[`rar_full_tiled_sequential_report.json`](../tests/end-to-end-generated/rar_full_tiled_sequential_report.json), and
[`rar_selected_par_vector_report.json`](../tests/end-to-end-generated/rar_selected_par_vector_report.json).
They record the complete optimized Loop text and per-case status, so the
structural counts can be independently recomputed; their elapsed times remain
descriptive measurements of that recorded run.

The large executable spot checks use
`tests/end-to-end-generated/rar_policy_param_tiers.json` with
`tools/end_to_end_c/run_generated_suite.py`; the JSON summaries record the full
PolOpt argument vectors, dimensions, repeat count, output comparison, and timing.

## Intuition

Think of a legal schedule as a large feasible region. RAW, WAR, and WAW
dependences define that region. RAR does not shrink it for correctness. Instead,
it changes the contours of the cost function inside the region, encouraging
reads of the same data to have a smaller transformed distance. The optimizer can
therefore land on a different legal point. Once tiling and annotation discovery
operate on that point, the final loop nest may look substantially different.

That is why no-RAR is a sound default, explicit RAR is a meaningful optimization
experiment, and neither policy should be trusted without the same downstream
PolCert checks.
