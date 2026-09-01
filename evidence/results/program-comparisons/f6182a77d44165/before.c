#define S1(zT3,zT4,zT5,$i0,$i1,$i2)	b[$i1][$i0] = b[$i1][$i0] / a[$i0][$i0];
#define S2(zT3,zT4,zT5,$i0,$i1,$i2)	b[$i1][$i2] = b[$i1][$i2] - a[$i0][$i2] * b[$i1][$i0];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 2) {
  for (t2=0;t2<=floord(N-2,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=t2;t6<=floord(N-1,32);t6++) {
        for (t7=32*t2;t7<=min(32*t2+31,32*t6-2);t7++) {
          for (t9=32*t4;t9<=min(N-1,32*t4+31);t9++) {
            for (t11=32*t6;t11<=min(N-1,32*t6+31);t11++) {
              S2(t2,t4,t6,t7,t9,t11);
            }
          }
        }
        for (t7=max(32*t2,32*t6-1);t7<=min(min(N-2,32*t2+31),32*t6+30);t7++) {
          for (t9=32*t4;t9<=min(N-1,32*t4+31);t9++) {
            S1(t2,t4,t6,t7,t9,(t7+1));
            for (t11=t7+1;t11<=min(N-1,32*t6+31);t11++) {
              S2(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
