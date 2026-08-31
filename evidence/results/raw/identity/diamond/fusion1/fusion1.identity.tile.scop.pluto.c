#define S1(zT1,$i0)	A[$i0] = 0.33 * In[$i0 - 1] + In[$i0] + In[$i0 + 1];
#define S2(zT1,$i0)	Out[$i0] = 0.33 * A[$i0 - 1] + A[$i0] + A[$i0 + 1];

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 4) {
  for (t2=0;t2<=floord(N-3,32);t2++) {
    for (t3=max(1,32*t2);t3<=min(N-3,32*t2+31);t3++) {
      S1(t2,t3);
    }
  }
  if (N >= 6) {
    for (t2=0;t2<=floord(N-4,32);t2++) {
      for (t3=max(2,32*t2);t3<=min(N-4,32*t2+31);t3++) {
        S2(t2,t3);
      }
    }
  }
}
/* End of CLooG code */
