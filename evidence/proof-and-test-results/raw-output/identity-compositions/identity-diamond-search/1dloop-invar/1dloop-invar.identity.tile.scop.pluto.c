#define S1($i0)	a[i] = b[i];

		int t1, t2, t3;

	register int lbv, ubv;

/* Start of CLooG code */
if (M <= N) {
  for (t2=M;t2<=N;t2++) {
    S1(t2);
  }
}
/* End of CLooG code */
