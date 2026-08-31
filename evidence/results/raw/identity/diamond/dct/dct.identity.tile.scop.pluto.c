#define S1(zT2,zT3,$i0,$i1)	temp2d[$i0][$i1] = 0.0;
#define S2(zT3,zT4,zT5,$i0,$i1,$i2)	temp2d[$i0][$i1] = temp2d[$i0][$i1] + block[$i0][$i2] * cos1[$i1][$i2];
#define S3(zT2,zT3,$i0,$i1)	sum2[$i0][$i1] = 0.0;
#define S4(zT3,zT4,zT5,$i0,$i1,$i2)	sum2[$i0][$i1] = sum2[$i0][$i1] + cos1[$i0][$i2] * temp2d[$i2][$i1];
#define S5(zT2,zT3,$i0,$i1)	block[$i0][$i1] = sum2[$i0][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12;

	register int lbv, ubv;

/* Start of CLooG code */
if (M >= 1) {
  for (t2=0;t2<=floord(M-1,32);t2++) {
    for (t4=0;t4<=floord(M-1,32);t4++) {
      for (t7=32*t2;t7<=min(M-1,32*t2+31);t7++) {
        for (t9=32*t4;t9<=min(M-1,32*t4+31);t9++) {
          S1(t2,t4,t7,t9);
        }
      }
      for (t6=0;t6<=floord(M-1,32);t6++) {
        for (t7=32*t2;t7<=min(M-1,32*t2+31);t7++) {
          for (t9=32*t4;t9<=min(M-1,32*t4+31);t9++) {
            for (t11=32*t6;t11<=min(M-1,32*t6+31);t11++) {
              S2(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(M-1,32);t2++) {
    for (t4=0;t4<=floord(M-1,32);t4++) {
      for (t7=32*t2;t7<=min(M-1,32*t2+31);t7++) {
        for (t9=32*t4;t9<=min(M-1,32*t4+31);t9++) {
          S3(t2,t4,t7,t9);
        }
      }
      for (t6=0;t6<=floord(M-1,32);t6++) {
        for (t7=32*t2;t7<=min(M-1,32*t2+31);t7++) {
          for (t9=32*t4;t9<=min(M-1,32*t4+31);t9++) {
            for (t11=32*t6;t11<=min(M-1,32*t6+31);t11++) {
              S4(t2,t4,t6,t7,t9,t11);
            }
          }
        }
      }
      for (t7=32*t2;t7<=min(M-1,32*t2+31);t7++) {
        for (t9=32*t4;t9<=min(M-1,32*t4+31);t9++) {
          S5(t2,t4,t7,t9);
        }
      }
    }
  }
}
/* End of CLooG code */
