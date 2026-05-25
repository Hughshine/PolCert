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

### 1.4 Parallel and vector family selection

- no parallel flag
  - stay sequential
- `--parallel`
  - use the Pluto-hinted parallel route
- `--parallel-strict`
  - refine `--parallel`: require the certified loop to match Pluto's hinted
    dimension
- `--multipar`
  - refine `--parallel`: use Pluto's multi-parallel hints and certify a list of
    current dimensions through the checked multi-current route
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
| `./polopt --iss --notile file.loop` | ISS + affine-only |
| `./polopt --iss --identity file.loop` | ISS-only checked split path |
| `./polopt --second-level-tile file.loop` | Sequential second-level tiling route |
| `./polopt --diamond-tile file.loop` | Sequential diamond phase route |
| `./polopt --full-diamond-tile file.loop` | Diamond route with stronger producer mode |
| `./polopt --parallel file.loop` | Pluto-hinted parallel route |
| `./polopt --parallel --parallel-strict file.loop` | Pluto-hinted route with strict hinted-dimension requirement |
| `./polopt --parallel --multipar file.loop` | Pluto-hinted multi-current checked parallel route |
| `./polopt --parallel-current d file.loop` | Explicit-dimension theorem-aligned parallel route |
| `./polopt --iss --parallel-current d file.loop` | ISS + explicit-dimension parallel route |
| `./polopt --vector file.loop` | Pluto-hinted checked vector route |
| `./polopt --vector-current d file.loop` | Explicit-dimension theorem-aligned vector route |

Two important details:

- `--full-diamond-tile` implies `--diamond-tile`
- `--parallel-strict` only makes sense as a refinement of `--parallel`
- `--multipar` only makes sense as a refinement of `--parallel`
- `--vector-strict` only makes sense as a refinement of `--vector`

The table above lists the important shapes, not every legal combination. In
particular:

- `--parallel` supports the checked Pluto-hinted one-current route on the
  normal affine/tiling, ISS, identity-tiling, second-level, and diamond-family
  compositions covered by the current wrapper
- `--parallel --multipar` follows the same hinted family but certifies a list of
  current dimensions through `RawParallelCurrentMany*` configs
- `--parallel-current d` supports:
  - default full tiled
  - `--notile`
  - `--identity`
  - `--iss`
  - `--iss --notile`
  - `--iss --identity`
- `--vector-current d` follows the same explicit-current support shape as
  `--parallel-current d`, but emits `vector for`
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

### 3.3 `--diamond-tile` chooses a distinct phase family

Rejected combinations:

- `--diamond-tile --second-level-tile`
- `--diamond-tile --band-tiling-experiment`
- `--diamond-tile --legacy-generic-tiling`

Reason:

- diamond means a dedicated phase family:
  - `affine(before, mid)`
  - `tiling(mid, posttile)`
  - optional `affine(posttile, after)`
- the current route map includes checked sequential, ISS-aware, and parallel
  diamond compositions, but diamond remains mutually exclusive with other
  tiling-family selectors

### 3.4 `--parallel` and `--parallel-current` choose different parallel families

Rejected combinations:

- `--parallel --parallel-current d`
- `--parallel-strict` without `--parallel`
- `--multipar` without `--parallel`

Reason:

- `--parallel` means "follow Pluto's hinted dimension if certification/codegen
  can make that work"
- `--multipar` refines that same family by asking for a checked list of hinted
  current dimensions
- `--parallel-current d` means "use the proved explicit-dimension route for
  current dimension `d`"
- hinted and explicit-current selection are different route families, so the
  frontend forces the user to pick one

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

## 4. How route selection actually works

The frontend makes the route choice in roughly this order:

1. If a standalone validation action is selected, run it and stop.
2. Otherwise, if `--vector-current d` is present, use the explicit-dimension
   vector family.
3. Otherwise, if `--parallel-current d` is present, use the explicit-dimension
   parallel family.
4. Otherwise, if `--vector` or `--prevector` is present, use the Pluto-hinted
   vector family.
5. Otherwise, if `--parallel` is present, use the Pluto-hinted parallel family; `--multipar` selects the multi-current variant inside that family.
6. Otherwise, if `--diamond-tile` is present, use the sequential diamond route.
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
  - checked and user-facing, including the `--multipar` multi-current variant
- second-level tiling
  - supported as a checked tiling family
- diamond tiling
  - supported as a theorem-backed opt-in route, with current ISS/parallel
    compositions documented in `doc/pluto-polopt-compatibility.md`

When in doubt, treat `--iss`, `--second-level-tile`, `--diamond-tile`,
`--parallel`, and `--parallel-current` as selectors for distinct pipeline
families rather than as independent booleans that should freely stack.

## 6. Assessment of the current flag model

The current flag model is partly principled and partly transitional.

### 6.1 What is already reasonable

Several current rejections are conceptually correct and should remain even
after a cleanup:

- standalone validation actions should stay separate from loop-to-loop
  optimization routes
- `--identity` and `--notile` should reject tiling-family flags, because those
  flags require a tiling artifact that does not exist on those routes
- `--parallel` and `--parallel-current` should remain distinct, because they
  choose different mechanisms for selecting the loop to parallelize
- storage-changing or overlap/reuse-style requests should remain rejected until
  the proof uses a state relation broader than `State.eq`

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

At that point the ordinary route becomes simpler:

- default ordinary band-aware tiling
- optional `--legacy-generic-tiling` only while comparison is still needed

### 7.4 Unify tiling-family selection more explicitly

Second-level and diamond are both tiling families, but they are currently
expressed through different flag relationships:

- second-level refines the ordinary family and is also allowed on tiling-only
  standalone actions
- diamond selects a narrower sequential route family with an optional stronger
  producer mode

That is defensible, but the documentation and implementation would become
clearer if the frontend treated tiling-family choice as one explicit layer with
sub-options, instead of several unrelated booleans.

### 7.5 Decide which future compositions are worth supporting

Not every currently rejected combination should become legal. The right next
questions are:

- which additional multi-current fixtures are useful now that the checked
  route can annotate every certified candidate dimension?
- should standalone tiling witness/validation actions grow a diamond-aware
  mode, or should diamond remain a loop-to-loop optimizer family only?
- which storage-changing families should move first to a generalized state
  relation?

These are proof-architecture questions, not just CLI questions. The flag model
should follow the supported proof combinations, not lead them.

### 7.6 Keep the error messages route-oriented

Even before a larger refactor, the rejection messages can improve by explaining
the route family conflict directly. For example:

- "diamond is currently a sequential non-ISS full-tiled family"
- "parallel-current selects a different parallel family than --parallel"
- "second-level only refines tiled routes and tiling-only validation actions"

This would make the current flat flag model much easier to understand in
practice.

## 8. Practical reading

The safest way to read `polopt` today is:

- accepted `file.loop` routes dispatch through the unified
  `Loop -> ParallelLoop` compiler wrapper
- `--iss`, `--parallel-current d`, `--parallel`, `--parallel-strict`, and
  `--parallel --multipar` are theorem-facing checked routes when accepted
- `--second-level-tile` and diamond flags are checked extensions of the tiled
  pipeline, with the current supported compositions documented in
  `doc/pluto-polopt-compatibility.md`
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
