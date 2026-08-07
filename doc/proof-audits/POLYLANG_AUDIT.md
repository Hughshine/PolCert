# `src/PolyLang.v` declaration and ownership audit

Scope: `proof/readability-cleanup`, read-only. The inventory includes explicit
top-level declarations, record projections, inductive constructors, and all 17
public notation aliases. No mutual `with` declaration occurs in this file.
Comments and strings are removed before building the call graph. External API
uses require an observed `PolyLang` instance/path; the repository contains no
`Import` or `Export PolyLang` that would make bare-name calls ambiguous.

## Counts

| Conceptual section | Declarations | Unique proof-body lines | Confirmed external roots | Reachable | Unreachable proof lines |
|---|---:|---:|---:|---:|---:|
| Representation, OpenScop, and current view | 135 | 146 | 55 | 116 | 17 |
| Implicit-point operational semantics | 13 | 95 | 4 | 7 | 94 |
| Normal instruction points and flattening | 100 | 1,482 | 60 | 77 | 509 |
| Extended old/new instruction points and flattening | 72 | 689 | 41 | 54 | 113 |
| Lexicographic sorting and stable permutation | 41 | 1,184 | 7 | 39 | 19 |
| PolyLex semantics | 12 | 123 | 8 | 10 | 0 |
| Schedule elimination for code generation | 28 | 409 | 9 | 23 | 117 |
| **Total** | **401** | **4,128** | **184** | **326** | **869** |

There are 40 exact zero-reference declarations and one self-recursive-only
definition (`refill_schedule_from_template`). All declarations are exported;
repository reachability does not prove absence of out-of-tree clients.

## Public surface

This file is a real public IR module, not an implementation-only proof file.
The highest-use names are representation and semantic boundaries:

| Name | Confirmed external source hits |
|---|---:|
| `ip_index` | 342 |
| `pi_depth` | 328 |
| `t` | 303 |
| `ip_nth` | 239 |
| `InstrPoint` | 174 |
| `instance_list_semantics` | 158 |
| `ip_time_stamp` | 152 |
| `wf_pprog_affine` | 141 |
| `PolyInstr` | 139 |
| `pi_poly` | 126 |
| `flatten_instrs` | 125 |
| `belongs_to` | 117 |

Consequently, public-name preservation must include notation aliases, record
projections, and constructors, not just theorem names.

## Correct ownership

PolyLang should continue to own:

- `PolyInstr`, program `t`, dimensions, current/base point views, witness-aware
  transformations, and well-formedness;
- normal and paired old/new instance representations used by validators;
- the declarative flattening contract and its connection to instruction-list
  semantics;
- implicit, instance-list, PolyLex, and schedule-elimination semantics;
- the semantic theorem that a permitted adjacent swap preserves execution.

The OpenScop encoder/decoder is a codec layer rather than the core semantic
model. It can eventually live behind a bridge module, but moving it before the
functor/API cleanup would create unnecessary generativity and dependency risk.

## Misowned utility

1. **List/sorted facts**: `NoDup_app`, `nth_error_Some'`, `Sorted_app`,
   `same_elem_lt_sorted_implies_same_list_pre`, and
   `forall_n_R_implies_rel_list` belong in `ListExt` or a sorted-list utility.
2. **Point ordering**: normal `np_lt`/`np_eq` and their order instances already
   conceptually belong to `InstanceListSema`; the normal comparator laws at
   5268--5622 should be proved there and re-exported here.
3. **Selection-sort mechanics**: mapping `select_helper`/`selsort`, moving one
   element across a prefix, deriving `ord_all` from sortedness, and proving
   selection sort is a stable permutation are parametric in the two order
   predicates. They belong in `SelectionSort.v`/`StablePermut.v`, not PolyLang.
4. **Vector/list algebra**: `insert_zeros_commute_after_env` is a generic,
   unreachable identity suitable for `LinalgExt` if retained.

Use thin theorems with the existing `PolyLang.<name>` and identical statements
after moving each canonical fact.

## Normal/ext flatten duplication

The two families repeat the same four-part contract:

1. environment prefix;
2. exact membership characterization;
3. `NoDup`;
4. sorting by `(instruction number, point index)`.

The normal/ext append proofs are 75/86 lines and the inverse proofs are 112/122
lines with the same rank partition and sorted-filter argument. Nil,
determinism, rank-bound, `np_lt`/`np_eq`, strict-order, and properness facts are
also duplicated.

Do not merge the public records: the ext form legitimately records old/new
schedules and an access transformation. Instead introduce a private generic
flattening skeleton parameterized by point/instruction types, rank, index,
membership, depth, and order. Instantiate its structural theorems twice and
retain every existing public definition/theorem statement.

`flatten_instrs_ext_app_singleton_inv` line 4826 says `unfold np_lt` while its
proof is about `np_lt_ext`. The following `left; lia` happens to close the goal,
but the command is misleading and brittle; make the ext relation explicit.

## Obsolete proof routes

- The 16-declaration `same_np_set`/length-contradiction route from 3086--3816 is
  unreachable and costs 499 proof-body lines. The live retiming route
  (`eqdom_pinstr_implies_flatten_instr_nth_retime` ->
  `flatten_instr_nth_det` -> primed relation theorems) is shorter and more
  direct.
- `eqdom_pinstr_implies_flatten_instr_nth_exists` manually repeats the later
  retimed-point construction in 97 lines. Move the retiming theorem earlier
  and make the existential theorem a short wrapper.
- `poly_semantics_k` and `poly_semantics_concat` form an unused implicit-scan
  branch. The latter duplicates the structure of live `poly_lex_concat`.
- Forty exact leaves are listed in the CSV. Larger leaves include
  `poly_semantics_concat` (71), `same_np_set_sorted_NoDupA_nth` (64),
  `eqdom_pinstr_implies_flatten_same_np_set` (58), and
  `insert_zeros_commute_after_env` (53).

## Stable permutation

The section mixes three layers:

1. lexicographic comparator laws;
2. generic selection-sort/stability theorems;
3. PolyLang semantic commutation of adjacent independent instructions.

Only layer 3 belongs here. `stable_permut_multi_skip` (200 lines) repeats the
same swap-admissibility proof twice. `select_helper_stable_permut` (232 lines)
is entirely generic. Move layers 1/2 downward, then define a local symmetric
semantic-equivalence predicate for instruction-point lists. Its reflexive,
symmetric, and transitive laws remove the duplicated forward/backward halves
of the 141-line adjacent-step theorem and the 66-line transitive closure.

`stable_permut'_ext_lists_are_equivalent` currently ends by filling two proof
evars with `Instr.State.dummy_state`. This is the only `dummy_state` use in the
file. It is caused by under-instantiated `eapply`/`eauto`, not by the theorem;
replace it with explicit state arguments. No semantic proof should depend on a
dummy state merely to satisfy elaboration.

## API-preserving remediation order

1. **Proof hygiene only**: remove the two dummy-state evars, correct the ext
   order name, name stable-swap side conditions, and add section headings.
   Public names and types remain byte-for-byte unchanged.
2. **Canonical retiming route**: move the live retiming theorem earlier and
   turn the 97-line existential result into a wrapper. Keep both names/types.
3. **Downstream generic utilities**: add parameterized theorems to
   `ListExt`, `InstanceListSema`, `SelectionSort`, and `StablePermut`; replace
   PolyLang proof bodies with exact wrappers.
4. **Private flatten skeleton**: instantiate shared normal/ext structural
   proofs while retaining current definitions and theorem statements.
5. **Semantic proof factoring**: introduce list-semantic equivalence and split
   adjacent swap from transitive closure; retain the three public stable
   equivalence theorem names.
6. **Dead-route decision last**: only remove the 75 unreachable exported names
   after deciding out-of-tree compatibility. Otherwise keep short wrappers or
   place the old proofs in a clearly labeled legacy section.
7. **Physical file split last**: consider an OpenScop bridge and dedicated
   flatten-proof file only after dependencies are acyclic and wrapper behavior
   has been compiled.

## P0/P1/P2 candidates

| Priority | Candidate | Evidence | Compatibility-preserving action |
|---|---|---|---|
| P0 | `stable_permut'_ext_lists_are_equivalent` | Lines 6662--6781 end with two `Instr.State.dummy_state` obligations created by under-instantiated automation. | Supply the actual state arguments explicitly; keep theorem name and type unchanged. |
| P0 | `flatten_instrs_ext_app_singleton_inv` | Line 4826 unfolds `np_lt` in the ext proof, whose intended relation is `np_lt_ext`. | Make the intended ext comparison explicit and compile the unchanged statement. |
| P0 | Public alias preservation | `ip_index`, `ip_nth`, and `InstrPoint` have respectively 342, 239, and 174 confirmed qualified external hits. | Treat notations, projections, and constructors as API during every move. |
| P1 | Retiming proof route | The 97-line `eqdom_pinstr_implies_flatten_instr_nth_exists` repeats the construction already captured by the 86-line retiming theorem; the older 16-declaration route is unreachable and costs 499 proof lines. | Put the retiming lemma first and reprove the existing existential theorem as a wrapper; retain the legacy route until compatibility is decided. |
| P1 | Generic list/order facts | `same_elem_lt_sorted_implies_same_list_pre` is 99 lines and depends only on list membership, sortedness, and order; several neighboring `NoDup`/`Sorted` lemmas are likewise parametric. | Move canonical proofs to `ListExt` or a sorted-list utility and leave exact-name/type wrappers in PolyLang. |
| P1 | Stable-sort mechanics | `stable_permut_multi_skip` and `select_helper_stable_permut` consume 200 and 232 proof lines and are independent of PolyLang execution semantics. | Move generic theorems to `StablePermut`/`SelectionSort`; retain PolyLang wrappers. |
| P1 | Normal/ext flatten structure | Append/inverse proofs consume 75/112 lines for normal points and 86/122 for ext points with the same rank partition. | Introduce a private parameterized structural layer, instantiate it twice, and preserve all public records and theorem statements. |
| P1 | Semantic adjacent swaps | The 141-line step theorem and 66-line closure repeat forward/backward semantic derivations. | Factor a private symmetric semantic-equivalence relation; expose the current three theorem names unchanged. |
| P2 | Dead exported families | 75 declarations are unreachable from confirmed repository clients; 40 have no exact reference, and the `same_np_set` route alone accounts for 499 proof lines. | Do not delete until out-of-tree compatibility is explicitly waived; otherwise mark legacy or retain wrappers. |
| P2 | OpenScop codec placement | Lines 150--1124 form a codec/normalization layer, but depend on the surrounding functor types. | Split only after the internal utility moves, avoiding a new generative functor boundary. |

## Generated evidence

- `/tmp/polcert-polylang-declarations.csv`
- `/tmp/polcert-polylang-declarations.md`
- `/tmp/polcert-polylang-external-refs.txt`
- `/tmp/polcert-polylang-rg-hits.txt`
- `/tmp/polcert-polylang-long-proofs.md`
