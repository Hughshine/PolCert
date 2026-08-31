#define S1(zT3,zT4,zT5,$i0,$i1,$i2)	C[$i0][$i1] = C[$i0][$i1] + A[$i0][$i2] * B[$i2][$i1];
#define S2(zT3,zT4,zT5,$i0,$i1,$i2)	D[$i0][$i1] = D[$i0][$i1] + C[$i0][$i2] * E[$i2][$i1];

		int t1, t2, t3, t4, t5, t6, t7, t8;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t1=0;t1<=floord(N-1,32);t1++) {
    for (t2=0;t2<=floord(N-1,32);t2++) {
      for (t4=0;t4<=floord(N-1,32);t4++) {
        for (t5=32*t1;t5<=min(N-1,32*t1+31);t5++) {
          for (t6=32*t2;t6<=min(N-1,32*t2+31);t6++) {
            for (t8=32*t4;t8<=min(N-1,32*t4+31);t8++) {
              S1(t1,t2,t4,t5,t6,t8);
            }
          }
        }
      }
      for (t4=0;t4<=floord(N-1,32);t4++) {
        for (t5=32*t1;t5<=min(N-1,32*t1+31);t5++) {
          for (t6=32*t2;t6<=min(N-1,32*t2+31);t6++) {
            for (t8=32*t4;t8<=min(N-1,32*t4+31);t8++) {
              S2(t1,t2,t4,t5,t8,t6);
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
