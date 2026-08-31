#define S1(zT3,zT4,$i0,$i1,$i2)	c[$i0][$i2] = c[$i0][$i2] + a[$i1][$i2] * b[$i0][$i1];
#define S2(zT3,zT4,$i0,$i1,$i2)	c[$i0][$i1] = c[$i0][$i1] + a[$i1][$i1] * b[$i0][$i1];
#define S3(zT2,zT3,$i0,$i1)	c[$i0][$i1] = c[$i0][$i1] + a[$i1][$i1] * b[$i0][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;

	register int lbv, ubv;

/* Start of CLooG code */
if (NMAX >= 1) {
  for (t2=0;t2<=floord(NMAX-1,32);t2++) {
    for (t4=0;t4<=floord(NMAX-1,32);t4++) {
      if ((NMAX >= 3) && (t4 == 0)) {
        for (t5=32*t2;t5<=min(NMAX-1,32*t2+31);t5++) {
          for (t7=0;t7<=1;t7++) {
            S3(t2,0,t5,t7);
          }
          for (t7=2;t7<=min(31,NMAX-1);t7++) {
            for (t9=0;t9<=t7-2;t9++) {
              S1(t2,0,t5,t7,t9);
              S2(t2,0,t5,t7,t9);
            }
            S3(t2,0,t5,t7);
          }
        }
      }
      if (t4 >= 1) {
        for (t5=32*t2;t5<=min(NMAX-1,32*t2+31);t5++) {
          for (t7=32*t4;t7<=min(NMAX-1,32*t4+31);t7++) {
            for (t9=0;t9<=t7-2;t9++) {
              S1(t2,t4,t5,t7,t9);
              S2(t2,t4,t5,t7,t9);
            }
            S3(t2,t4,t5,t7);
          }
        }
      }
      if ((NMAX <= 2) && (t2 == 0) && (t4 == 0)) {
        for (t5=0;t5<=NMAX-1;t5++) {
          for (t7=0;t7<=NMAX-1;t7++) {
            S3(0,0,t5,t7);
          }
        }
      }
    }
  }
}
/* End of CLooG code */
