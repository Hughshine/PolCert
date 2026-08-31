#define S1(zT2,zT3,$i0,$i1)	d[$i1] = d[$i1] + a[$i0][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8;

	register int lbv, ubv;

/* Start of CLooG code */
if ((M >= 1) && (N >= 1)) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(M-1,32);t4++) {
      for (t5=32*t2;t5<=min(N-1,32*t2+31);t5++) {
        for (t7=32*t4;t7<=min(M-1,32*t4+31);t7++) {
          S1(t2,t4,t5,t7);
        }
      }
    }
  }
}
/* End of CLooG code */
