#define S1(zT3,zT4,$i0,$i1,$i2)	B[$i1][$i0] = B[$i1][$i0] - L[$i1][$i2] * B[$i2][$i0];
#define S2(zT2,zT3,$i0,$i1)	B[$i1][$i0] = B[$i1][$i0] / L[$i1][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      if ((N >= 2) && (t4 == 0)) {
        for (t5=32*t2;t5<=min(N-1,32*t2+31);t5++) {
          S2(t2,0,t5,0);
          for (t7=1;t7<=min(31,N-1);t7++) {
            for (t9=0;t9<=t7-1;t9++) {
              S1(t2,0,t5,t7,t9);
            }
            S2(t2,0,t5,t7);
          }
        }
      }
      if (t4 >= 1) {
        for (t5=32*t2;t5<=min(N-1,32*t2+31);t5++) {
          for (t7=32*t4;t7<=min(N-1,32*t4+31);t7++) {
            for (t9=0;t9<=t7-1;t9++) {
              S1(t2,t4,t5,t7,t9);
            }
            S2(t2,t4,t5,t7);
          }
        }
      }
      if ((N == 1) && (t2 == 0) && (t4 == 0)) {
        S2(0,0,0,0);
      }
    }
  }
}
/* End of CLooG code */
