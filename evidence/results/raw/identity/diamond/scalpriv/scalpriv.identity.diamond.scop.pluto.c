#define S1($i0)	a = 0;
#define S2($i0)	b[$i0] = a;

		int t1, t2, t3;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=N-1;t2++) {
    S1(t2);
    S2(t2);
  }
}
/* End of CLooG code */
