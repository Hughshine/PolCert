#define S1(zT3,zT4,zT5,$i0,$i1,$i2)	ab[$i0][$i1][$i2] = f60 * a[$i0 - 1][$i1][$i2] + a[$i0][$i1][$i2] + f61 * a[$i0 - 2][$i1][$i2] + a[$i0 + 1][$i1][$i2] + f62 * a[$i0 - 3][$i1][$i2] + a[$i0 + 2][$i1][$i2] * thirddtbydy * uyb[$i0][$i1][$i2];
#define S2(zT3,zT4,zT5,$i0,$i1,$i2)	al[$i0][$i1][$i2] = f60 * a[$i0][$i1 - 1][$i2] + a[$i0][$i1][$i2] + f61 * a[$i0][$i1 - 2][$i2] + a[$i0][$i1 + 1][$i2] + f62 * a[$i0][$i1 - 3][$i2] + a[$i0][$i1 + 2][$i2] * thirddtbydx * uxl[$i0][$i1][$i2];
#define S3(zT3,zT4,zT5,$i0,$i1,$i2)	af[$i0][$i1][$i2] = f60 * a[$i0][$i1][$i2 - 1] + a[$i0][$i1][$i2] + f61 * a[$i0][$i1][$i2 - 2] + a[$i0][$i1][$i2 + 1] + f62 * a[$i0][$i1][$i2 - 3] + a[$i0][$i1][$i2 + 2] * thirddtbydz * uzf[$i0][$i1][$i2];
#define S4(zT3,zT4,zT5,$i0,$i1,$i2)	athird[$i0][$i1][$i2] = a[$i0][$i1][$i2] + al[$i0][$i1 + 1][$i2] - al[$i0][$i1][$i2] + ab[$i0 + 1][$i1][$i2] - ab[$i0][$i1][$i2] + af[$i0][$i1][$i2 + 1] - af[$i0][$i1][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12;

	register int lbv, ubv;

/* Start of CLooG code */
if ((nx >= -3) && (nx >= -nz-5) && (ny >= -3) && (ny >= -nx-5) && (ny >= -nz-5) && (nz >= -3)) {
  if ((nx >= -2) && (nz >= -2)) {
    for (t2=0;t2<=floord(ny+7,32);t2++) {
      for (t4=0;t4<=floord(nx+6,32);t4++) {
        for (t6=0;t6<=floord(nz+6,32);t6++) {
          for (t7=max(4,32*t2);t7<=min(ny+7,32*t2+31);t7++) {
            for (t9=max(4,32*t4);t9<=min(nx+6,32*t4+31);t9++) {
              for (t11=max(4,32*t6);t11<=min(nz+6,32*t6+31);t11++) {
                S1(t2,t4,t6,t7,t9,t11);
              }
            }
          }
        }
      }
    }
  }
  if ((ny >= -2) && (nz >= -2)) {
    for (t2=0;t2<=floord(ny+6,32);t2++) {
      for (t4=0;t4<=floord(nx+7,32);t4++) {
        for (t6=0;t6<=floord(nz+6,32);t6++) {
          for (t7=max(4,32*t2);t7<=min(ny+6,32*t2+31);t7++) {
            for (t9=max(4,32*t4);t9<=min(nx+7,32*t4+31);t9++) {
              for (t11=max(4,32*t6);t11<=min(nz+6,32*t6+31);t11++) {
                S2(t2,t4,t6,t7,t9,t11);
              }
            }
          }
        }
      }
    }
  }
  if ((nx >= -2) && (ny >= -2)) {
    for (t2=0;t2<=floord(ny+6,32);t2++) {
      for (t4=0;t4<=floord(nx+6,32);t4++) {
        for (t6=0;t6<=floord(nz+7,32);t6++) {
          for (t7=max(4,32*t2);t7<=min(ny+6,32*t2+31);t7++) {
            for (t9=max(4,32*t4);t9<=min(nx+6,32*t4+31);t9++) {
              for (t11=max(4,32*t6);t11<=min(nz+7,32*t6+31);t11++) {
                S3(t2,t4,t6,t7,t9,t11);
              }
            }
          }
        }
      }
    }
  }
  if ((nx >= -2) && (ny >= -2) && (nz >= -2)) {
    for (t2=0;t2<=floord(ny+6,32);t2++) {
      for (t4=0;t4<=floord(nx+6,32);t4++) {
        for (t6=0;t6<=floord(nz+6,32);t6++) {
          for (t7=max(4,32*t2);t7<=min(ny+6,32*t2+31);t7++) {
            for (t9=max(4,32*t4);t9<=min(nx+6,32*t4+31);t9++) {
              for (t11=max(4,32*t6);t11<=min(nz+6,32*t6+31);t11++) {
                S4(t2,t4,t6,t7,t9,t11);
              }
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
