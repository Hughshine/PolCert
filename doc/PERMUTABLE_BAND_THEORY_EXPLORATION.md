# Permutable-Band Validation: Theory Boundary and Runtime Design

This note fixes the specification boundary of the direct permutable-band
validator and records how the executable route realizes that boundary.

## 1. Three different correctness questions

### 1.1 Pluto rectangular-tiling legality

Let a band start at schedule depth `p` and contain affine hyperplanes
`phi[p], ..., phi[p + width - 1]`. Let `E_p` contain the dependences that
have not already been satisfied before depth `p`.

For the standard rectangular strip-mine/interchange construction considered
by Pluto, the band is fully permutable exactly when every residual dependence
has a nonnegative component in every band dimension:

```text
forall e : S_i -> S_j in E_p,
forall (s, t) in P_e,
forall k in the band,
  phi[k](S_j, t) - phi[k](S_i, s) >= 0.
```

Together with independent hyperplanes, this is the necessary-and-sufficient
condition for each dimension to be a legal tiling hyperplane and for the band
to remain legal under arbitrary permutations, in the sense of Bondhugula's
thesis, Definition 12 and Theorem 1.

This is not a necessary condition for every fixed tiled target. A dependence
vector such as `(1, -1)` is not fully permutable, but a particular tile size or
fixed tile-loop order can preserve that dependence. The condition also does
not by itself characterize tilings that cross scalar scattering dimensions or
arbitrary nonrectangular tilings.

### 1.2 PolCert semantic band permutability

PolCert should not trust Pluto's dependence polyhedra. Its semantic analogue
of the condition above is:

```text
source_order(tau1, tau2) /\
same_prefix_before_band(tau1, tau2) /\
band_component_decreases(k, tau1, tau2)
  -> Permutable_ext(tau1, tau2).
```

Equivalently, every source-ordered, noncommuting pair with the same outer
prefix must be nondecreasing in every band component. This is the semantic
counterpart of Pluto's residual-dependence condition: a genuine semantic
dependence is represented by a nonpermutable pair rather than by trusting an
external dependence edge.

The semantic condition and Pluto's dependence condition coincide only under
an exact correspondence between dependence edges and source-ordered
nonpermutable instance pairs. A conservative dependence graph can make
Pluto's geometric condition strictly stronger.

### 1.3 Equivalence of one concrete tiled target

For a checked rectangular tiling structure, semantic band permutability is
sufficient for `State.eq` between the source-scheduled and tiled executions:

```text
checked tiling shape
  + semantic permutable-band property
  + every target reversal exposes a decreasing band component
  -> every target reversal swaps only permutable instances
  -> State.eq.
```

The converse is false in general. One particular target may preserve the
order of a problematic pair, a chosen tile size may keep both instances in
one tile, or whole-program effects may coincide without admitting a proof by
pairwise commutation. Therefore the validator should claim soundness, not an
iff characterization of arbitrary program equivalence.

## 2. The soundness statement

The central semantic result has the following shape:

```text
Theorem checked_rectangular_tiling_via_permutable_band_sound:
  check_tiling_shape before after witness = true ->
  check_permutable_bands before witness bands = true ->
  semantics after st1 st2 ->
  exists st2',
    semantics before st1 st2' /\ State.eq st2 st2'.
```

The proof factors through two independently visible lemmas:

```text
check_permutable_bands = true -> semantic_permutable_bands

semantic_permutable_bands + checked_tiling_shape
  -> tiling_reordering_safe
```

Using a generic reordering-safety lemma inside the proof is appropriate. The
executable band checker must nevertheless check the band condition itself.

## 3. Direct bad-pair checker

For each statement pair and each band component, construct the counterexample
region

```text
domain(s) /\ domain(t)
/\ same_environment(s, t)
/\ old_schedule(s) < old_schedule(t)
/\ prefix_before_band(s) = prefix_before_band(t)
/\ phi[k](s) > phi[k](t)
/\ conflicting_access(s, t).
```

The band component is valid when every WW, WR, and RW counterexample region
is certified empty. All components must be valid.

The implementation reuses the existing certified primitives:

- `make_poly_lt` for the source-order disjunction;
- `make_poly_eq` for prefix equality;
- `make_constr_gt` for the decreasing component;
- access composition and same-location constraints;
- `isBottom` certificates;
- `no_write_collision_implies_permutable`.

This shares the conflict and polyhedral-emptiness kernel with affine
translation validation, but it neither constructs a synthetic schedule nor
invokes the complete affine-validator interface.

## 4. Proof obligations and nonclaims

Required:

1. Soundness of prefix-equality constraints.
2. Soundness of the selected-component decrease constraint.
3. Soundness of each empty bad-pair query for WW, WR, and RW conflicts.
4. Aggregation from no collision to `Permutable_ext`.
5. Program-level aggregation over statement pairs and band components.
6. The structural reversal bridge for each supported tiling variant.
7. End-to-end `State.eq` through the existing tiling semantics.

Desirable but separate:

- relative completeness for the supported affine-access fragment;
- an iff characterization of the current synthetic-schedule reduction;
- proof that repeated tiling preserves the band condition.

Do not claim:

- completeness of `isBottom` unless the oracle interface supports it;
- necessity of the band condition for one arbitrary concrete target;
- equivalence with a conservative Pluto dependence graph without an exactness
  hypothesis;
- that whole-program affine validation establishes a permutable band.

## 5. Runtime design and proved coverage

The runtime has three observable outcomes:

```text
permutable-band   a direct band checker and a tiling-specific reversal bridge
                  establish reordering safety
general-fallback  a complete source/target affine validation, the canonical
                  validator, or the general tiling validator succeeds
rejected          no validator accepts the candidate
```

Only the first outcome is a permutable-band result. In particular, the legacy
whole-schedule checker is never relabeled as a band result. An attempted
"actual-target residual" wrapper was removed after proving it definitionally
equal to the existing complete affine pair traversal.

The direct implementation establishes the following facts:

1. The common-band checker constructs the source-order, equal-prefix, and
   decreasing-component guards directly. It checks all WW, WR, and RW
   conflicts for self pairs, both directions of every distinct statement pair,
   and every component of the band.
2. Guard soundness and collision-freedom lemmas turn successful checks into the
   semantic permutable-band property. This layer reuses the certified access
   conflict and polyhedral-emptiness kernel, but it does not call the complete
   affine schedule validator.
3. Ordinary rectangular tiling, diamond tiling, and full-diamond tiling use the
   common-band checker. The final affine phase of a diamond pipeline remains a
   separate affine-validation step.
4. Strict second-level schedules use a componentwise direct checker. The
   structural classifier accepts both exact grouped tile coordinates and exact
   interleaved root/child tile coordinates; Pluto's diamond plus second-level
   output uses the latter layout. A layout-parameterized local reversal theorem
   proves that every relevant target reversal identifies the same band for both
   statements and exposes a decreasing component in that band. The checker
   therefore need not impose obligations on statement pairs with distinct band
   records unless the bridge can make such a pair relevant.
5. The second-level classifier also accepts insertion or deletion of strictly
   zero schedule rows at the end of every statement, while keeping one uniform
   grouped or interleaved layout for the whole program. The proof shows that
   the expected and imported timestamps differ only by trailing zeros and are
   therefore equivalent for lexicographic comparison. This rule does not erase
   internal zero rows and does not provide the global slot mapping needed by
   source-like identity schedules.
6. Both direct paths end in `pprog_tiling_reordering_safe`, then reuse the
   source-based tiling theorem to obtain `State.eq`. The executable dispatcher
   returns `permutable-band` only from one of these two theorem chains.
7. Program, witness, inferred-band, and composed-instruction lengths are
   checked before component queries. A mismatch returns `false` without
   invoking the polyhedral solver. Impure solver failure cannot be converted
   into an accepted route.
8. A frozen negative dependence has a decreasing component inside the proposed
   band. The direct checker, the legacy strong checker, and the complete affine
   checker all reject it without an alarm.

### 5.1 Zero-normalized identity schedules

Pluto may omit strict-zero scattering rows independently for each statement.
For example, a mixed-depth target can have this layout:

```text
statement 1: tile(4) ++ zero tile padding ++ source(3) ++ zero source padding
statement 2: tile(5)                       ++ source(4)
```

Deleting zero rows statement by statement is not a sound cross-statement
normalization: a row absent from one statement can be a real varying schedule
component in another. A direct proof requires a program-wide mapping from
global tile slots to zero-extended source components, common positive tile
sizes, and a proof that pointwise order of the padded source timestamps implies
pointwise order of the padded tile timestamps.

That normalization theorem is not part of the current runtime. Ordinary
identity and mixed-depth identity schedules therefore report
`general-fallback`. They remain verified by the existing complete validator,
but they are not counted as direct permutable-band cases. Strict second-level
instances that satisfy the existing common-start and common-recipe shape gate
continue to use the proved componentwise direct route.

## 6. Reproduction Notes

The following wall-clock times were observed on the current machine and
checkout. They are planning estimates rather than performance claims.

- Recompiling `TilingBandScheduleValidator.vo` after a proof edit took about
  43 seconds.
- Regenerating extraction after invalidating its Coq dependency closure took
  about 9 minutes. Incremental OCaml relinking was much shorter.
- The five-case direct differential gate took 8.38 seconds with warm binaries.
- The 90-case one-level route matrix took 176.49 seconds: 50 direct-band
  successes, 34 explicit fallbacks, and 6 explicit vector rejections.
- The complete second-level tiling suite took 947.89 seconds, about 16 minutes.
  Its route contract contained 36 direct-band successes and 17 explicit
  fallbacks, plus the standalone trailing-zero and rejection regressions and
  the 16-success/4-rejection diamond matrix.

The Coq and OCaml builds used `hughshine/polcert:latest`. Diamond execution
tests used Pluto commit `6f43860` from `gifted_curie`; that is also the commit
currently checked out at `/pluto` in the container. A new artifact image must
pin and verify the same revision before running the route suites.
