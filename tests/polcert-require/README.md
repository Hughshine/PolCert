# polcert --require fixtures

`dfp-skew.before.scop` is `polopt`'s export of `dfp-skew.loop`.
`dfp-skew.after.scop` is the schedule Pluto proposes for it with `--dfp`. The
proposal gives the conflicting pair `S2(2,2)`, which writes `A[3][4][7]`, and
`S1(2,3)`, which reads it when `N = 5`, the same timestamp `(2,6)`. The after
model therefore admits both orders of the pair, and only the converse
refinement holds: `polcert` reports `[LT]` and, under the default
`--require refines`, exits 1. Swapping the files gives `[GT]` and exit 0;
either file against itself gives `[EQ]`.

`tools/regression/check_polcert_require.py` checks the exit status of each
`--require` value on these pairs (`make test-polcert-require`).
