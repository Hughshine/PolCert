#define S1($i0)	A[$i0] = 0.33 * In[$i0 - 1] + In[$i0] + In[$i0 + 1];
#define S2($i0)	Out[$i0] = 0.33 * A[$i0 - 1] + A[$i0] + A[$i0 + 1];

		int t1, t2;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 4) {
  for (t1=1;t1<=min(2,N-3);t1++) {
    S1(t1);
  }
  for (t1=3;t1<=N-3;t1++) {
    S1(t1);
    S2((t1-1));
  }
}
/* End of CLooG code */
