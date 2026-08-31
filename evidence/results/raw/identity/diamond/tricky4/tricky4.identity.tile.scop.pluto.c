#define S1($i0)	s = s + 1;

		int t1, t2, t3;

	register int lbv, ubv;

/* Start of CLooG code */
if (M <= 0) {
  for (t2=0;t2<=-M;t2++) {
    S1(t2);
  }
}
/* End of CLooG code */
