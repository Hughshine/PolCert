#define S1(zT2,$i0,$i1)	e[$i1] = e[$i1] - coeff1 * h[$i1] - h[$i1 - 1];
#define S2(zT2,$i0,$i1)	h[$i1] = h[$i1] - coeff2 * e[$i1 + 1] - e[$i1];

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 1) && (T >= 1)) {
  for (t2=1;t2<=T;t2++) {
    if (N >= 2) {
      for (t4=0;t4<=floord(N-1,32);t4++) {
        for (t5=max(1,32*t4);t5<=min(N-1,32*t4+31);t5++) {
          S1(t4,t2,t5);
        }
      }
    }
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t5=32*t4;t5<=min(N-1,32*t4+31);t5++) {
        S2(t4,t2,t5);
      }
    }
  }
}
/* End of CLooG code */
