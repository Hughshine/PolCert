#define S1(zT2,$i0,$i1)	b[$i1] = 0.33333 * a[$i1 - 1] + a[$i1] + a[$i1 + 1];
#define S2(zT2,$i0,$i1)	a[$i1] = b[$i1];

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 4) && (T >= 1)) {
  for (t2=0;t2<=T-1;t2++) {
    for (t4=0;t4<=floord(N-2,32);t4++) {
      for (t5=max(2,32*t4);t5<=min(N-2,32*t4+31);t5++) {
        S1(t4,t2,t5);
      }
    }
    for (t4=0;t4<=floord(N-2,32);t4++) {
      for (t5=max(2,32*t4);t5<=min(N-2,32*t4+31);t5++) {
        S2(t4,t2,t5);
      }
    }
  }
}
/* End of CLooG code */
