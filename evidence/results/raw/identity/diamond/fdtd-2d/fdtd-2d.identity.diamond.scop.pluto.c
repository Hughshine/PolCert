#define S1(zT2,$i0,$i1)	ey[0][$i1] = $i0;
#define S2(zT3,zT4,$i0,$i1,$i2)	ey[$i1][$i2] = ey[$i1][$i2] - 0.5 * hz[$i1][$i2] - hz[$i1 - 1][$i2];
#define S3(zT3,zT4,$i0,$i1,$i2)	ex[$i1][$i2] = ex[$i1][$i2] - 0.5 * hz[$i1][$i2] - hz[$i1][$i2 - 1];
#define S4(zT3,zT4,$i0,$i1,$i2)	hz[$i1][$i2] = hz[$i1][$i2] - 0.7 * ex[$i1][$i2 + 1] - ex[$i1][$i2] + ey[$i1 + 1][$i2] - ey[$i1][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;

	register int lbv, ubv;

/* Start of CLooG code */
if ((ny >= 1) && (tmax >= 1)) {
  for (t2=0;t2<=tmax-1;t2++) {
    for (t4=0;t4<=floord(ny-1,32);t4++) {
      for (t5=32*t4;t5<=min(ny-1,32*t4+31);t5++) {
        S1(t4,t2,t5);
      }
    }
    if (nx >= 2) {
      for (t4=0;t4<=floord(nx-1,32);t4++) {
        for (t6=0;t6<=floord(ny-1,32);t6++) {
          for (t7=max(1,32*t4);t7<=min(nx-1,32*t4+31);t7++) {
            for (t9=32*t6;t9<=min(ny-1,32*t6+31);t9++) {
              S2(t4,t6,t2,t7,t9);
            }
          }
        }
      }
    }
    if (ny >= 2) {
      for (t4=0;t4<=floord(nx-1,32);t4++) {
        for (t6=0;t6<=floord(ny-1,32);t6++) {
          for (t7=32*t4;t7<=min(nx-1,32*t4+31);t7++) {
            for (t9=max(1,32*t6);t9<=min(ny-1,32*t6+31);t9++) {
              S3(t4,t6,t2,t7,t9);
            }
          }
        }
      }
    }
    for (t4=0;t4<=floord(nx-1,32);t4++) {
      for (t6=0;t6<=floord(ny-1,32);t6++) {
        for (t7=32*t4;t7<=min(nx-1,32*t4+31);t7++) {
          for (t9=32*t6;t9<=min(ny-1,32*t6+31);t9++) {
            S4(t4,t6,t2,t7,t9);
          }
        }
      }
    }
  }
}
/* End of CLooG code */
