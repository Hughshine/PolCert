#define S1(zT2,$i0,$i1)	a[$i0][$i1] = a[$i0][$i1] / a[$i0][$i0];
#define S2(zT3,zT4,$i0,$i1,$i2)	a[$i1][$i2] = a[$i1][$i2] - a[$i1][$i0] * a[$i0][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 2) {
  for (t2=0;t2<=N-2;t2++) {
    for (t4=ceild(t2-30,32);t4<=floord(N-1,32);t4++) {
      for (t5=max(32*t4,t2+1);t5<=min(N-1,32*t4+31);t5++) {
        S1(t4,t2,t5);
      }
    }
    for (t4=ceild(t2-30,32);t4<=floord(N-1,32);t4++) {
      for (t6=ceild(t2-30,32);t6<=floord(N-1,32);t6++) {
        for (t7=max(32*t4,t2+1);t7<=min(N-1,32*t4+31);t7++) {
          for (t9=max(32*t6,t2+1);t9<=min(N-1,32*t6+31);t9++) {
            S2(t4,t6,t2,t7,t9);
          }
        }
      }
    }
  }
}
/* End of CLooG code */
