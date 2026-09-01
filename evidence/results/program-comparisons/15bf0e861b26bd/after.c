#define S1(zT2,$i0,$i1)	A[$i0][$i1] = A[$i0 + -1 * 1][K] + 1;

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if ((M >= 1) && (N >= 2)) {
  for (t2=1;t2<=N-1;t2++) {
    for (t4=0;t4<=floord(M-1,32);t4++) {
      for (t5=32*t4;t5<=min(M-1,32*t4+31);t5++) {
        S1(t4,t2,t5);
      }
    }
  }
}
/* End of CLooG code */
