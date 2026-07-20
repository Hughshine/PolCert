# Permutable-Band Validation: Theory Boundary and Direct-Checker Plan

This note fixes the specification boundary for the direct permutable-band
validator. It is an exploration artifact. It does not change the existing
runtime route or proofs.

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

## 2. The theorem we should claim

The central semantic result should have the following shape:

```text
Theorem checked_rectangular_tiling_via_permutable_band_sound:
  check_tiling_shape before after witness = true ->
  check_permutable_bands before witness bands = true ->
  semantics after st1 st2 ->
  exists st2',
    semantics before st1 st2' /\ State.eq st2 st2'.
```

The proof should factor through two independently visible lemmas:

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

The implementation can reuse the existing certified primitives:

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

## 5. Exploration status

The isolated prototype currently establishes the following facts:

1. Under explicit component-existence bounds, the current synthetic schedule
   has a reversal exactly when the source prefix is equal and the selected
   component decreases. This iff theorem is compiled, but it does not imply
   completeness of the affine validator or of the heterogeneous wrapper.
2. A dormant common-band checker directly constructs the old-order and bad
   component polyhedra and checks all WW, WR, and RW collision combinations.
3. The checker covers self pairs, both directions of every distinct statement
   pair, and every component in the common band.
4. Compiled guard-soundness lemmas show that a semantic bad pair belongs to
   both generated polyhedron lists.
5. A compiled checker-result theorem turns successful guard queries into the
   absence of WW, WR, and RW collisions, and then into `Permutable_ext` for the
   concrete instance pair.
6. Compiled aggregation theorems cover arbitrary ordered statement pairs, all
   dimensions of the common band, and the program-level common-band wrapper.
   The final wrapper proves the same strong common-band proposition as the
   legacy synthetic-schedule checker.
7. Extraction and OCaml builds succeed. Automated differential checks report
   `old-strong=true`, `direct-band=true`, and `whole=true`, with no alarms, for
   ordinary and a frozen diamond phase pair. A mixed-depth example reports
   `false`, `false`, and `true`, respectively, which is the intended
   distinction between the common-band and whole-program scopes. Separate
   phase-pair checks give `true`, `true`, and `true` for both Pluto diamond
   modes on the current example; both modes produce the same frozen pair.
8. The 90-case one-level route matrix passes unchanged: 84 compositions use
   the permutable-band route, six non-innermost vector requests are rejected,
   and no case uses the general fallback.

The direct wrapper is still disconnected from the runtime dispatcher. The
remaining work is to support heterogeneous and second-level bands, connect the
direct wrapper without weakening the existing inference precondition, add a
frozen negative dependence case, and reuse the existing strong-property proof
to obtain the final `State.eq` theorem for the new route. Identity and the
current second-level fixture do not pass the common-band inference gate; their
existing specialized routes remain unchanged.

## 6. Reproduction Notes

The following wall-clock times were observed on the current machine and
checkout. They are planning estimates rather than performance claims.

- Recompiling `TilingBandScheduleValidator.vo` after a proof edit took about
  43 seconds.
- Regenerating extraction after invalidating its Coq dependency closure took
  about 7 minutes. Incremental OCaml relinking was much shorter.
- The four-case direct differential gate took about 8 seconds with warm
  binaries.
- The 90-case one-level route matrix took about 3 minutes.
- The complete second-level tiling suite took about 18 minutes.

The Coq and OCaml builds used `hughshine/polcert:latest`. Diamond execution
tests used Pluto commit `6f43860` from `gifted_curie`. The Pluto binary currently
stored in that image reports commit `7cb0892`; it is not the execution baseline
for the diamond and full-diamond results above. A new artifact image must pin
and verify `6f43860` before running the route suites.
