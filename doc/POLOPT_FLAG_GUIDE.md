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

These flags matter on ordinary full-tiled routes and on the explicit
identity-tiled route. Tiling-only standalone actions also accept the
second-level selector.

- no tiling-family flag
  - default ordinary tiling route, currently using the band-aware checked
    tiling validator
- `--legacy-generic-tiling`
  - deprecated compatibility alias for the default band-first ordinary route
- `--band-tiling-experiment`
  - compatibility alias for the current default band-aware ordinary tiling
    route
- `--second-level-tile`
  - switch the producer to hierarchical second-level tiling; validation still
    enters the common permutable-band-first dispatcher
- `--diamond-tile`
  - switch the producer/checker pair to the sequential diamond phase family
- `--full-diamond-tile`
  - same checked route as `--diamond-tile`, but with the stronger Pluto
    producer mode

These flags answer: if a tiling phase exists, which tiling family should
produce and validate it?

### 1.4 Parallel and vector family selection

- no parallel flag
  - stay sequential
- `--parallel`
  - use the Pluto-hinted parallel route
- `--parallel-strict`
  - refine `--parallel`: require the certified loop to match Pluto's hinted
    dimension
- `--parallel-current d`
  - use the theorem-aligned explicit-dimension parallel route
- `--vector`, `--prevector`
  - use Pluto's vector loop hint when possible, then certify a doall current
    dimension and emit `vector for`
- `--vector-strict`
  - refine `--vector`: require the certified loop to match Pluto's vector hint
- `--vector-current d`
  - use the theorem-aligned explicit-dimension vector route

These flags answer: do we stay sequential, follow Pluto's hint, or certify a
user-selected current dimension? Vector routes reuse the same parallel/doall
checker because Pluto's prevector marker is derived from parallel-loop analysis.

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
| `./polopt --second-level-tile file.loop` | Sequential second-level tiling route |
| `./polopt --diamond-tile file.loop` | Sequential diamond phase route |
| `./polopt --full-diamond-tile file.loop` | Diamond route with stronger producer mode |
| `./polopt --parallel file.loop` | Pluto-hinted parallel route |
| `./polopt --parallel --parallel-strict file.loop` | Pluto-hinted route with strict hinted-dimension requirement |
| `./polopt --parallel-current d file.loop` | Explicit-dimension theorem-aligned parallel route |
| `./polopt --iss --parallel-current d file.loop` | ISS + explicit-dimension parallel route |
| `./polopt --vector file.loop` | Pluto-hinted checked vector route |
| `./polopt --vector-current d file.loop` | Explicit-dimension theorem-aligned vector route |

Two important details:

- `--full-diamond-tile` implies `--diamond-tile`
- `--parallel-strict` only makes sense as a refinement of `--parallel`
- `--vector-strict` only makes sense as a refinement of `--vector`

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
- `--vector-current d` follows the same explicit-current support shape as
  `--parallel-current d`, but emits `vector for`
- bare sequential `--iss --identity` and `--iss --notile` are rejected; their
  ISS identity/affine variants require a checked parallel or vector consumer
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
  - `--parallel-strict`
  - `--diamond-tile`
  - `--band-tiling-experiment`
  - `--legacy-generic-tiling`
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

### 3.2 Tiling selectors require an actual tiling producer

`--notile` rejects second-level and diamond tiling because it stops before a
tiling phase exists. Diamond tiling also rejects `--identity`, which produces no
Pluto schedule. Identity second-level tiling is supported only with `--tile`
(or the `--identity-tiled` alias), so that Pluto supplies the tiled schedule to
validate.

### 3.3 Diamond and second-level families compose with checked consumers

Diamond and second-level tiling can be followed by ISS, hinted or
explicit-current parallelization, vectorization, and multipar consumers. These
options do not replace tiling validation: the produced tiling artifact still
enters the same permutable-band-first dispatcher before any consumer is
applied.

`--diamond-tile` and `--full-diamond-tile` are alternative strengths of the
diamond producer. Either may be combined with `--second-level-tile`; this asks
Pluto for nested diamond tiling and validates that nested result. The
compatibility-only `--band-tiling-experiment` and
`--legacy-generic-tiling` aliases do not compose with diamond or second-level
tiling.

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
- either legacy selector with `--second-level-tile`
- `--band-tiling-experiment` with the same families above

Reason:

- both flags are compatibility names for the ordinary full-tiled default route
- they are not general modifiers for every pipeline family
- both aliases now select the same permutable-band-first validator; the legacy
  name is retained only for command-line compatibility

## 4. How route selection actually works

The frontend makes the route choice in roughly this order:

1. If a standalone validation action is selected, run it and stop.
2. Otherwise, if `--vector-current d` is present, use the explicit-dimension
   vector family.
3. Otherwise, if `--parallel-current d` is present, use the explicit-dimension
   parallel family.
4. Otherwise, if `--vector` or `--prevector` is present, use the Pluto-hinted
   vector family.
5. Otherwise, if `--parallel` is present, use the Pluto-hinted parallel family.
6. Otherwise, if `--diamond-tile` is present, use the diamond producer/phase
   family; a checked sequential, parallel, vector, or multipar consumer may
   adopt its result.
7. Otherwise, choose among:
   - default route
   - `--iss`
   - `--notile`
   - `--identity`
   - optional ordinary-tiling refinements such as `--legacy-generic-tiling`

This explains why some flags feel "stronger" than others: some choose the whole
route family, while others only refine a family that is already selected.

## 5. Current support boundary in one page

The current support boundary is:

- ordinary sequential route
  - default and stable
- ISS route
  - supported and theorem-aligned
- explicit-dimension parallel route
  - theorem-aligned
- Pluto-hinted parallel route
  - experimental but user-facing
- second-level tiling
  - supported with sequential, ISS, identity-tiled, parallel, vector, and
    multipar consumers
- diamond tiling
  - supported in normal and full forms
  - supported with ISS, second-level tiling, parallel, vector, and multipar
    consumers

The producer family (ordinary, second-level, or diamond) and a later consumer
(ISS, parallel, or vector) are separate choices. The route normalizer rejects
only combinations for which no coherent producer or consumer exists.

## 6. Assessment of the current flag model

The current flag model is partly principled and partly transitional.

### 6.1 What is already reasonable

Several current rejections are conceptually correct and should remain even
after a cleanup:

- standalone validation actions should stay separate from loop-to-loop
  optimization routes
- `--notile` should reject tiling-family flags, and identity tiling should
  require an explicit tiled identity route
- `--parallel` and `--parallel-current` should remain distinct, because they
  choose different mechanisms for selecting the loop to parallelize
- compatibility-only ordinary-tiling aliases should not silently alter or
  disappear inside another tiling family

These are semantic constraints, not parser accidents.

### 6.2 What is still awkward

The main awkwardness is no longer route normalization itself. That part already
exists in [syntax/SLoopRoute.ml](../syntax/SLoopRoute.ml): the parser state is
collapsed into an explicit selection over:

- optimize vs standalone validation
- base route
- structural extension
- tiling family
- parallel family

The remaining awkwardness is around how the CLI gets there:

- the parser still starts from many flat booleans before normalization
- producer-family choices and checker-family choices still share one top-level
  command surface
- new families such as diamond or second-level still need help-text and
  rejection-message updates in several places

So the current status is:

- the supported combinations themselves are mostly reasonable
- the normalized route model is in place
- the remaining cleanup is about parser shape, command structure, and
  user-facing messaging

### 6.3 The biggest conceptual rough edge

The largest remaining design mismatch is that `polopt` currently exposes both:

- loop-to-loop optimizer routes
- standalone validation actions over external files

in the same top-level command.

That is historically convenient, but conceptually it mixes two tools:

- optimizer family selection
- validator-only artifact checking

The current exclusions keep this workable, but they also make the flag space
look more irregular than the underlying framework really is.

## 7. TODO plan for flag cleanup

The following cleanup plan would make the current model easier to maintain.

### 7.1 Keep route normalization as the single source of truth

That refactor is already mostly done. The current route-spec style selection in
[syntax/SLoopRoute.ml](../syntax/SLoopRoute.ml) already owns legality checking
and normalized family selection, while CLI-side setup still performs some
downstream mode wiring. The cleanup goal is to keep normalized selection in
`SLoopRoute` as the single source of truth for:

- optimize vs standalone validation
- base route / structural extension
- tiling family
- parallel family

The next cleanup step is not "invent a route-spec", but rather:

- keep parser/help text synchronized with the normalized selection
- drive scheduler/setup helpers from the normalized selection instead of raw
  booleans where practical
- avoid duplicating legality rules in ad hoc command handlers
- continue making rejection messages describe route-family conflicts directly

### 7.2 Separate optimizer mode from standalone validation mode

The cleanest user model would be:

- `polopt ...` for loop-to-loop optimization
- `polcert ...` for external artifact validation

or, if `polopt` keeps these actions:

- explicit subcommands such as `polopt optimize ...` and `polopt validate ...`

This would eliminate the current need to explain why route flags and
validation-only actions cannot be mixed.

### 7.3 Retire compatibility-only tiling flags

`--band-tiling-experiment` is already documented and implemented as a
compatibility alias for the default ordinary checked tiling route.

The likely next step is:

- keep it temporarily for backward compatibility
- mark it as deprecated in help text
- eventually remove it

`--legacy-generic-tiling` is likewise only a deprecated command-line alias; it
does not select a generic-primary validator and should be retired with the
experiment alias. The ordinary route has one validation policy regardless of
which compatibility spelling selected it.

### 7.4 Unify tiling-family selection more explicitly

Second-level and diamond are both tiling families, but they are currently
expressed through different flag relationships:

- second-level refines the ordinary family and is also allowed on tiling-only
  standalone actions
- diamond selects a producer/phase family with an optional stronger producer
  mode; checked consumers are selected independently

That is defensible, but the documentation and implementation would become
clearer if the frontend treated tiling-family choice as one explicit layer with
sub-options, instead of several unrelated booleans.

### 7.5 Keep future compositions theorem-led

The current producer families already compose with ISS and the checked
parallel/vector consumers. Further combinations should be exposed only when
their end-to-end route is represented by the extracted dispatcher and its
top-level correctness theorem. Standalone witness/validation actions remain
separate because they consume external artifacts rather than a `.loop`
pipeline.

### 7.6 Keep the error messages route-oriented

Even before a larger refactor, the rejection messages can improve by explaining
the route family conflict directly. For example:

- "diamond requires a tiled producer and cannot be combined with identity or
  notile"
- "parallel-current selects a different parallel family than --parallel"
- "second-level only refines tiled routes and tiling-only validation actions"

This would make the current flat flag model much easier to understand in
practice.

## 8. Practical reading

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
