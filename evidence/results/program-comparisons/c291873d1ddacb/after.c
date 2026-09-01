#define S1(zT5,zT6,zT7,zT8,zT9,$i0,$i1,$i2,$i3,$i4)	T1[$i0][$i1][$i2][$i3] = T1[$i0][$i1][$i2][$i3] + A[$i4][$i1][$i2][$i3] * C4[$i4][$i0];
#define S2(zT5,zT6,zT7,zT8,zT9,$i0,$i1,$i2,$i3,$i4)	T2[$i0][$i1][$i2][$i3] = T2[$i0][$i1][$i2][$i3] + T1[$i0][$i4][$i2][$i3] * C3[$i4][$i1];
#define S3(zT5,zT6,zT7,zT8,zT9,$i0,$i1,$i2,$i3,$i4)	T3[$i0][$i1][$i2][$i3] = T3[$i0][$i1][$i2][$i3] + T2[$i0][$i1][$i4][$i3] * C2[$i4][$i2];
#define S4(zT5,zT6,zT7,zT8,zT9,$i0,$i1,$i2,$i3,$i4)	B[$i0][$i1][$i2][$i3] = B[$i0][$i1][$i2][$i3] + T3[$i0][$i1][$i2][$i4] * C1[$i4][$i3];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t8=0;t8<=floord(N-1,32);t8++) {
          for (t10=0;t10<=floord(N-1,32);t10++) {
            for (t11=32*t2;t11<=min(N-1,32*t2+31);t11++) {
              for (t13=32*t4;t13<=min(N-1,32*t4+31);t13++) {
                for (t15=32*t6;t15<=min(N-1,32*t6+31);t15++) {
                  for (t17=32*t8;t17<=min(N-1,32*t8+31);t17++) {
                    for (t19=32*t10;t19<=min(N-1,32*t10+31);t19++) {
                      S1(t2,t4,t6,t8,t10,t11,t13,t15,t17,t19);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t8=0;t8<=floord(N-1,32);t8++) {
          for (t10=0;t10<=floord(N-1,32);t10++) {
            for (t11=32*t2;t11<=min(N-1,32*t2+31);t11++) {
              for (t13=32*t4;t13<=min(N-1,32*t4+31);t13++) {
                for (t15=32*t6;t15<=min(N-1,32*t6+31);t15++) {
                  for (t17=32*t8;t17<=min(N-1,32*t8+31);t17++) {
                    for (t19=32*t10;t19<=min(N-1,32*t10+31);t19++) {
                      S2(t2,t4,t6,t8,t10,t11,t13,t15,t17,t19);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t8=0;t8<=floord(N-1,32);t8++) {
          for (t10=0;t10<=floord(N-1,32);t10++) {
            for (t11=32*t2;t11<=min(N-1,32*t2+31);t11++) {
              for (t13=32*t4;t13<=min(N-1,32*t4+31);t13++) {
                for (t15=32*t6;t15<=min(N-1,32*t6+31);t15++) {
                  for (t17=32*t8;t17<=min(N-1,32*t8+31);t17++) {
                    for (t19=32*t10;t19<=min(N-1,32*t10+31);t19++) {
                      S3(t2,t4,t6,t8,t10,t11,t13,t15,t17,t19);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t4=0;t4<=floord(N-1,32);t4++) {
      for (t6=0;t6<=floord(N-1,32);t6++) {
        for (t8=0;t8<=floord(N-1,32);t8++) {
          for (t10=0;t10<=floord(N-1,32);t10++) {
            for (t11=32*t2;t11<=min(N-1,32*t2+31);t11++) {
              for (t13=32*t4;t13<=min(N-1,32*t4+31);t13++) {
                for (t15=32*t6;t15<=min(N-1,32*t6+31);t15++) {
                  for (t17=32*t8;t17<=min(N-1,32*t8+31);t17++) {
                    for (t19=32*t10;t19<=min(N-1,32*t10+31);t19++) {
                      S4(t2,t4,t6,t8,t10,t11,t13,t15,t17,t19);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
