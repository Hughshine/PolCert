#define S1(zT1,$i0)	symmat[$i0][$i0] = 1.0;
#define S2(zT2,zT3,$i0,$i1)	symmat[$i0][$i1] = 0.0;
#define S3(zT3,zT4,zT5,$i0,$i1,$i2)	symmat[$i0][$i1] = symmat[$i0][$i1] + data[$i2][$i0] * data[$i2][$i1];
#define S4(zT2,zT3,$i0,$i1)	symmat[$i1][$i0] = symmat[$i0][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12;

	register int lbv, ubv;

/* Start of CLooG code */
if (M >= 2) {
  for (t2=0;t2<=floord(M-1,32);t2++) {
    for (t7=max(1,32*t2);t7<=min(M-1,32*t2+31);t7++) {
      S1(t2,t7);
    }
    for (t4=t2;t4<=floord(M,32);t4++) {
      for (t7=max(1,32*t2);t7<=min(min(M-1,32*t2+31),32*t4+30);t7++) {
        for (t9=max(32*t4,t7+1);t9<=min(M,32*t4+31);t9++) {
          S2(t2,t4,t7,t9);
        }
      }
      if (N >= 1) {
        for (t6=0;t6<=floord(N,32);t6++) {
          for (t7=max(1,32*t2);t7<=min(min(M-1,32*t2+31),32*t4+30);t7++) {
            for (t9=max(32*t4,t7+1);t9<=min(M,32*t4+31);t9++) {
              for (t11=max(1,32*t6);t11<=min(N,32*t6+31);t11++) {
                S3(t2,t4,t6,t7,t9,t11);
              }
            }
          }
        }
      }
      for (t7=max(1,32*t2);t7<=min(min(M-1,32*t2+31),32*t4+30);t7++) {
        for (t9=max(32*t4,t7+1);t9<=min(M,32*t4+31);t9++) {
          S4(t2,t4,t7,t9);
        }
      }
    }
  }
}
/* End of CLooG code */
