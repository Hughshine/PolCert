#define S1(zT3,zT4,zT5,$i0,$i1,$i2)	sum[$i0][$i1][$i2] = 0;
#define S2(zT4,zT5,zT6,zT7,$i0,$i1,$i2,$i3)	sum[$i0][$i1][$i2] = sum[$i0][$i1][$i2] + A[$i0][$i1][$i3] * C4[$i3][$i2];
#define S3(zT3,zT4,zT5,$i0,$i1,$i2)	A[$i0][$i1][$i2] = sum[$i0][$i1][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t9=32*t2;t9<=min(N-1,32*t2+31);t9++) {
          for (t11=32*t4;t11<=min(N-1,32*t4+31);t11++) {
            for (t13=32*t6;t13<=min(N-1,32*t6+31);t13++) {
              S1(t2,t4,t6,t9,t11,t13);
            }
          }
        }
        for (t8=0;t8<=floord(N-1,32);t8++) {
          for (t9=32*t2;t9<=min(N-1,32*t2+31);t9++) {
            for (t11=32*t4;t11<=min(N-1,32*t4+31);t11++) {
              for (t13=32*t6;t13<=min(N-1,32*t6+31);t13++) {
                for (t15=32*t8;t15<=min(N-1,32*t8+31);t15++) {
                  S2(t2,t4,t6,t8,t9,t11,t13,t15);
                }
              }
            }
          }
        }
      }
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t9=32*t2;t9<=min(N-1,32*t2+31);t9++) {
          for (t11=32*t4;t11<=min(N-1,32*t4+31);t11++) {
            for (t13=32*t6;t13<=min(N-1,32*t6+31);t13++) {
              S3(t2,t4,t6,t9,t11,t13);
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
