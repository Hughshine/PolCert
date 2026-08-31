#define S1(zT3,zT4,zT5,$i0,$i1,$i2)	C[$i0][$i1] = C[$i0][$i1] + A[$i0][$i2] * B[$i2][$i1];
#define S2(zT3,zT4,zT5,$i0,$i1,$i2)	F[$i0][$i1] = F[$i0][$i1] + D[$i0][$i2] * E[$i2][$i1];
#define S3(zT3,zT4,zT5,$i0,$i1,$i2)	G[$i0][$i1] = G[$i0][$i1] + C[$i0][$i2] * F[$i2][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t7=32*t2;t7<=min(N-1,32*t2+31);t7++) {
          for (t9=32*t4;t9<=min(N-1,32*t4+31);t9++) {
            for (t11=32*t6;t11<=min(N-1,32*t6+31);t11++) {
              S1(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t7=32*t2;t7<=min(N-1,32*t2+31);t7++) {
          for (t9=32*t4;t9<=min(N-1,32*t4+31);t9++) {
            for (t11=32*t6;t11<=min(N-1,32*t6+31);t11++) {
              S2(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t7=32*t2;t7<=min(N-1,32*t2+31);t7++) {
          for (t9=32*t4;t9<=min(N-1,32*t4+31);t9++) {
            for (t11=32*t6;t11<=min(N-1,32*t6+31);t11++) {
              S3(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
