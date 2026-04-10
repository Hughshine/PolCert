# `polopt` Flag Guide

This note explains the user-facing flag model implemented by the `polopt` CLI.
Today that surface is split across:

- [syntax/SLoopCli.ml](../syntax/SLoopCli.ml): argument parsing and usage text
- [syntax/SLoopRoute.ml](../syntax/SLoopRoute.ml): route normalization and
  rejected-combination checks
- [syntax/SLoopDispatch.ml](../syntax/SLoopDispatch.ml): dispatch over the
  normalized route families
- [syntax/SLoopMain.ml](../syntax/SLoopMain.ml): thin executable shell over the
  shared helpers above

The short version is:

- some flags choose which verified pipeline family to run
- some flags refine one family
- some flags bypass optimization entirely and run standalone validation actions
- some flags only control printing, profiling, or extraction

Many rejected combinations are not arbitrary. They are blocked because the
selected flags would ask `polopt` to combine two different pipeline families,
or would request a feature at a point in the pipeline where the necessary
artifact does not exist.

## 1. Pipeline layers

`polopt` is easiest to understand if its flags are grouped by layer.

### 1.1 Base route shape

Exactly one of these route shapes is active for a normal optimization run:

- default full tiled route
  - extracted, strengthened, affine-scheduled, then tiling is attempted
- `--notile`
  - stops after the affine scheduling stage
- `--identity`
  - skips Pluto scheduling entirely and runs extract/strengthen/codegen only

These flags answer: how far through the optimizer pipeline should we go?

### 1.2 Structural extension

- `--iss`
  - switches from the default route family to the ISS-aware family

This is not just a printer option. It changes the pipeline family itself by
inserting the checked ISS structural stage before later scheduling.

### 1.3 Tiling family selection

These flags only matter on full tiled routes.

- no tiling-family flag
  - default ordinary tiling route, currently using the band-aware checked
    tiling validator
- `--legacy-generic-tiling`
  - use the historical generic ordinary-tiling validator instead of the
    default band-aware route
- `--band-tiling-experiment`
  - compatibility alias for the current default band-aware ordinary tiling
    route
- `--second-level-tile`
  - switch the producer/checker pair to the hierarchical second-level tiling
    family
- `--diamond-tile`
  - switch the producer/checker pair to the sequential diamond phase family
- `--full-diamond-tile`
  - same checked route as `--diamond-tile`, but with the stronger Pluto
    producer mode

These flags answer: if a tiling phase exists, which tiling family should
produce and validate it?

### 1.4 Parallel family selection

- no parallel flag
  - stay sequential
- `--parallel`
  - use the Pluto-hinted parallel route
- `--parallel-strict`
  - refine `--parallel`: require the certified loop to match Pluto's hinted
    dimension
- `--parallel-current d`
  - use the theorem-aligned explicit-dimension parallel route

These flags answer: do we stay sequential, follow Pluto's hint, or certify a
user-selected current dimension?

### 1.5 Standalone validation actions

These do not optimize a `.loop` program. They bypass the normal loop-to-loop
route and instead validate external artifacts directly.

- `--validate-affine-openscop before.scop after.scop`
- `--extract-tiling-witness-openscop before.scop after.scop`
- `--validate-tiling-openscop before.scop after.scop`
- `--validate-iss-debug-dumps before.txt after.txt`
- `--validate-iss-bridge bridge.txt`
- `--validate-iss-pluto-suite`
- `--validate-iss-pluto-live-suite`

### 1.6 Observation and debugging flags

These do not choose a different proof object. They only change what gets
printed or profiled.

- `--dump-input`
- `--dump-extracted-openscop`
- `--dump-scheduled-openscop`
- `--debug-scheduler`
- `--profile-stages`
- `--extract-only`

`--extract-only` is the one exceptional flag here: it short-circuits the run
after extraction. Most route-selection flags therefore become irrelevant when
it is used, and `--parallel-current` is rejected explicitly because there is no
parallel-current extraction-only route.

## 2. Main optimization families

The practically important user-visible route shapes are:

| Command shape | Meaning |
| --- | --- |
| `./polopt file.loop` | Default sequential affine+ordinary-tiling route |
| `./polopt --notile file.loop` | Sequential affine-only route |
| `./polopt --identity file.loop` | Identity/no-Pluto route |
| `./polopt --iss file.loop` | ISS + affine + ordinary tiling |
| `./polopt --iss --notile file.loop` | ISS + affine-only |
| `./polopt --iss --identity file.loop` | ISS-only checked split path |
| `./polopt --second-level-tile file.loop` | Sequential second-level tiling route |
| `./polopt --diamond-tile file.loop` | Sequential diamond phase route |
| `./polopt --full-diamond-tile file.loop` | Diamond route with stronger producer mode |
| `./polopt --parallel file.loop` | Pluto-hinted parallel route |
| `./polopt --parallel --parallel-strict file.loop` | Pluto-hinted route with strict hinted-dimension requirement |
| `./polopt --parallel-current d file.loop` | Explicit-dimension theorem-aligned parallel route |
| `./polopt --iss --parallel-current d file.loop` | ISS + explicit-dimension parallel route |

Two important details:

- `--full-diamond-tile` implies `--diamond-tile`
- `--parallel-strict` only makes sense as a refinement of `--parallel`

The table above lists the important shapes, not every legal combination. In
particular:

- `--parallel` supports:
  - default full tiled
  - `--notile`
  - `--iss`
  - `--iss --notile`
- `--parallel-current d` supports:
  - default full tiled
  - `--notile`
  - `--identity`
  - `--iss`
  - `--iss --notile`
  - `--iss --identity`
- `--second-level-tile` is also valid with:
  - `--extract-tiling-witness-openscop`
  - `--validate-tiling-openscop`

## 3. Why some combinations are rejected

### 3.1 Standalone validation actions cannot be mixed with pipeline selectors

Rejected combinations:

- any standalone validation action together with:
  - `--identity`
  - `--notile`
  - `--iss`
  - `--parallel`
  - `--diamond-tile`
- any standalone validation action together with `--parallel-current`

Reason:

- standalone actions consume external artifacts directly
- pipeline selectors choose how to optimize a `.loop` program
- mixing them would ask the frontend to do two different jobs at once

One deliberate exception exists:

- `--second-level-tile` is allowed with tiling witness extraction and tiling
  validation

Reason:

- second-level tiling changes the tiling-family parser/importer for those
  actions
- it does not ask for a second pipeline family

### 3.2 `--identity` and `--notile` reject tiling-family flags

Rejected combinations:

- `--second-level-tile --identity`
- `--second-level-tile --notile`
- `--diamond-tile --identity`
- `--diamond-tile --notile`

Reason:

- second-level and diamond are tiling-family selectors
- `--identity` creates no Pluto scheduling artifact at all
- `--notile` stops before any tiling phase exists

### 3.3 `--diamond-tile` is currently a narrow sequential family

Rejected combinations:

- `--diamond-tile --iss`
- `--diamond-tile --parallel`
- `--diamond-tile --parallel-current d`
- `--diamond-tile --second-level-tile`
- `--diamond-tile --band-tiling-experiment`
- `--diamond-tile --legacy-generic-tiling`

Reason:

- diamond currently means a dedicated sequential phase family:
  - `affine(before, mid)`
  - `tiling(mid, posttile)`
  - optional `affine(posttile, after)`
- that family is not yet wired together with ISS, the theorem-aligned explicit
  parallel routes, or the Pluto-hinted parallel routes

### 3.4 `--parallel` and `--parallel-current` choose different parallel families

Rejected combinations:

- `--parallel --parallel-current d`
- `--parallel-strict` without `--parallel`

Reason:

- `--parallel` means "follow Pluto's hinted dimension if certification/codegen
  can make that work"
- `--parallel-current d` means "use the proved explicit-dimension route for
  current dimension `d`"
- those are different route families, so the frontend forces the user to pick
  one

### 3.5 Legacy ordinary-tiling selectors are intentionally narrow

Rejected combinations:

- `--legacy-generic-tiling` with:
  - `--identity`
  - `--notile`
  - `--iss`
  - `--parallel`
  - `--parallel-current`
- `--band-tiling-experiment` with the same families above

Reason:

- both flags are about how the ordinary full-tiled default route validates
  tiling
- they are not general modifiers for every pipeline family

## 4. Practical reading

The safest way to read `polopt` today is:

- `file.loop`, `--iss`, and `--parallel-current d` are theorem-aligned user
  routes with dedicated proof objects
- `--parallel` / `--parallel-strict` are verified components exposed through an
  experimental CLI family
- `--second-level-tile` and diamond flags are checked extensions of the tiled
  pipeline, but not the default theorem object
- standalone validation actions are artifact checkers, not optimization routes

When in doubt, first decide:

1. am I optimizing a `.loop`, or validating an external artifact?
2. if I am optimizing, which route family do I want:
   - default
   - ISS
   - explicit parallel-current
   - Pluto-hinted parallel
   - special tiling family

That mental model matches the route normalization now implemented in
[syntax/SLoopRoute.ml](../syntax/SLoopRoute.ml).
