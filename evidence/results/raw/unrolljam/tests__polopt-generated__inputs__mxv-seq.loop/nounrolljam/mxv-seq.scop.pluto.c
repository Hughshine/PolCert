#define S1(zT2,zT3,$i0,$i1)	y[$i0] = y[$i0] + a[$i0][$i1] * x[$i1];
#define S2(zT2,zT3,$i0,$i1)	z[$i0] = z[$i0] + b[$i0][$i1] * y[$i1];

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t1=0;t1<=floord(N-1,32);t1++) {
    for (t3=0;t3<=floord(N-1,32);t3++) {
      for (t4=32*t1;t4<=min(N-1,32*t1+31);t4++) {
        for (t6=32*t3;t6<=min(N-1,32*t3+31);t6++) {
          S1(t1,t3,t4,t6);
        }
      }
    }
    for (t3=0;t3<=floord(N-1,32);t3++) {
      for (t4=32*t1;t4<=min(N-1,32*t1+31);t4++) {
        for (t6=32*t3;t6<=min(N-1,32*t3+31);t6++) {
          S2(t1,t3,t6,t4);
        }
      }
    }
  }
}
/* End of CLooG code */
