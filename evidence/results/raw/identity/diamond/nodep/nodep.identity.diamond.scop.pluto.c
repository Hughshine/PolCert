#define S1(zT2,zT3,$i0,$i1)	A[4 * $i0 + $i1] = 2 * A[4 * $i0 + $i1] + 2;

		int t1, t2, t3, t4, t5, t6, t7, t8;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=3;t2++) {
  for (t5=32*t2;t5<=min(99,32*t2+31);t5++) {
    for (t7=0;t7<=3;t7++) {
      S1(t2,0,t5,t7);
    }
  }
}
/* End of CLooG code */
