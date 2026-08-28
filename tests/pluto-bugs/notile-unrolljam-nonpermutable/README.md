# No-tile unroll-jam crosses a non-permutable loop

Status: reproduced, minimized, validator-catches.

The outer `i,h` loops form a permutable band. The `j` loop carries a
dependence: iteration `j + 1` reads element `a[...,j,3]`, which iteration `j`
writes only when the inner `k` loop reaches `3`.

At pinned Pluto commit `488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02`,
the unroll-jam candidate search unconditionally treats the program as having
one tiled level. With `--notile`, that skips the real band boundary and admits
the non-permutable `j` loop. Pluto then emits adjacent `j` and `j + 1`
statements inside the `k` loop. At `k = 0`, the second statement reads
`a[...,j,3]` before it has been written.

The original program prints `15`; Pluto's generated program prints `1`.
PolCert's checked unroll-jam route does not emit the unsafe adjacent pair.

Run the complete producer and validator check with:

```sh
python3 tools/pluto_bugs/run_notile_unrolljam_nonpermutable.py
```
