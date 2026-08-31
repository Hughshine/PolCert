# Fusion5 scalar-interleaved tiling fixtures

These OpenScop files freeze the ordinary tiling phase boundary for
`tests/polopt-generated/inputs/fusion5.loop`.

- Pluto repository: `phase-dump-pluto-fork`
- Pluto commit: `diamond-regression-snapshot`
- Source loop SHA-256:
  `b229b09e0581e02027d42a182dccad4e07d01b7fcc9a3d2fb7c60dfd7e5a9bdb`
- Extracted source OpenScop SHA-256:
  `50dc87dffd154becc9520f1a418da5c99c864ca280b3f2333a121c232355d616`
- Midpoint SHA-256:
  `4a52ec690857d1d97028a260f30d03cb301af7301b5c7ab0fe58f43ce93b5e9a`
- Posttile SHA-256:
  `253abb02692581bc2d70e14d15f83d71cdeb0cbbb1adea7a5a7888e44fbd3e38`

Generation used the repository's `polopt --extract-only` command, followed by
these two phase-separated Pluto invocations:

```text
pluto --dumpscop --readscop --nointratileopt --nodiamond-tile \
  --noprevector --smartfuse --nounrolljam --noparallel --notile --rar \
  source.scop

pluto --dumpscop --readscop --identity --tile --nointratileopt \
  --nodiamond-tile --noprevector --nounrolljam --noparallel --rar \
  midpoint.scop
```

The midpoint schedule has the form `loop, scalar, loop`. Pluto preserves and
interleaves the scalar components in the tiled schedule:
`tile, scalar, tile, point, scalar, point`. The regression test derives three
negative inputs from the frozen posttile file by deleting the first scalar
component, moving it across the following band component, or changing its
statement-specific constant.
