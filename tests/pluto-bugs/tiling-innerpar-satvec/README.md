# Inner-Parallel Tiling Metadata Corrupts Dependence Satisfaction

Status: reproduced, minimized, validator-catches.

The two-dimensional recurrence reads both `a[i-1][j]` and `a[i][j-1]`.
The rectangular tiling transformation is legal, but neither original schedule
dimension is parallel.

With `--identity --tile --parallel --innerpar`, pinned Pluto leaves the tile
schedule unchanged in `lib/tile.c:446-456`. It nevertheless moves inner
dependence-satisfaction bits to the outer tile dimension and clears the inner
bits at `lib/tile.c:461-478`. Later parallel-loop discovery trusts those bits
and emits an OpenMP pragma for tile loop `t4`.

The fixture uses tile size `2`, so the 16-by-16 recurrence contains several
tiles while all source values remain within signed 32-bit range. The original
program prints `310235039`. Four-thread executions of Pluto's output produce
different values. PolCert separates the two claims:

- the checked permutable-band validator accepts the rectangular tiling itself;
- the parallel validator finds no certifiable nontrivial dimension and refuses
  Pluto's unsafe OpenMP annotation;
- non-strict mode emits the safe tiled loop with only a one-iteration parallel
  loop, which is semantically sequential, while strict mode rejects the
  requested parallel optimization without output.

Run the executable comparison and the phase-specific checks with:

```sh
opam exec -- make test-pluto-miscompilation-tiling-innerpar
```
