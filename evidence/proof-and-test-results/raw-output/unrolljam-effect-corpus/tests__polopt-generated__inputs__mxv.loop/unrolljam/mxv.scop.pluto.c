#define S1(zT1,$i0)	y[$i0] = 0;
#define S2(zT2,zT3,$i0,$i1)	y[$i0] = y[$i0] + a[$i0][$i1] * x[$i1];

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t3=32*t2;t3<=min(N-1,32*t2+31);t3++) {
      S1(t2,t3);
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t3=0;t3<=floord(N-1,32);t3++) {
      for (t4=32*t2;t4<=(min(N-1,32*t2+31))-3;t4+=4) {
        for (t5=32*t3;t5<=min(N-1,32*t3+31);t5++) {
          S2(t2,t3,t4,t5);
          S2(t2,t3,(t4+1),t5);
          S2(t2,t3,(t4+2),t5);
          S2(t2,t3,(t4+3),t5);
        }
      }
      for (;t4<=min(N-1,32*t2+31);t4++) {
        for (t5=32*t3;t5<=min(N-1,32*t3+31);t5++) {
          S2(t2,t3,t4,t5);
        }
      }
    }
  }
}
/* End of CLooG code */
