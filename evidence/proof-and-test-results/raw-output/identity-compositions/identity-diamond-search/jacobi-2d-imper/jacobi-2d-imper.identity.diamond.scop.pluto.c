#define S1(zT3,zT4,$i0,$i1,$i2)	b[$i1][$i2] = 0.2 * a[$i1][$i2] + a[$i1][$i2 - 1] + a[$i1][1 + $i2] + a[1 + $i1][$i2] + a[$i1 - 1][$i2];
#define S2(zT3,zT4,$i0,$i1,$i2)	a[$i1][$i2] = b[$i1][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 4) && (T >= 1)) {
  for (t2=0;t2<=T-1;t2++) {
    for (t4=0;t4<=floord(N-2,32);t4++) {
      for (t6=0;t6<=floord(N-2,32);t6++) {
        for (t7=max(2,32*t4);t7<=min(N-2,32*t4+31);t7++) {
          for (t9=max(2,32*t6);t9<=min(N-2,32*t6+31);t9++) {
            S1(t4,t6,t2,t7,t9);
          }
        }
      }
    }
    for (t4=0;t4<=floord(N-2,32);t4++) {
      for (t6=0;t6<=floord(N-2,32);t6++) {
        for (t7=max(2,32*t4);t7<=min(N-2,32*t4+31);t7++) {
          for (t9=max(2,32*t6);t9<=min(N-2,32*t6+31);t9++) {
            S2(t4,t6,t2,t7,t9);
          }
        }
      }
    }
  }
}
/* End of CLooG code */
