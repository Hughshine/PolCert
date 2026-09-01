#define S1(zT3,zT4,zT5,$i0,$i1,$i2)	c[$i1][$i2] = c[$i1][$i2] + a[$i0][$i1] * a[$i0][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12;

	register int lbv, ubv;

/* Start of CLooG code */
if (NMAX >= 1) {
  for (t2=0;t2<=floord(NMAX-1,32);t2++) {
    for (t4=0;t4<=floord(NMAX-1,32);t4++) {
      for (t6=t4;t6<=floord(NMAX-1,32);t6++) {
        for (t7=32*t2;t7<=min(NMAX-1,32*t2+31);t7++) {
          for (t9=32*t4;t9<=min(NMAX-1,32*t4+31);t9++) {
            for (t11=max(32*t6,t9);t11<=min(NMAX-1,32*t6+31);t11++) {
              S1(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
