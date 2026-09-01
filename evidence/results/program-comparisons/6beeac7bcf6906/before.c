#define S1(zT1,$i0)	a[$i0] = $i0 + 7;

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,64);t2++) {
    for (t3=32*t2;t3<=min(floord(N-1,2),32*t2+31);t3++) {
      S1(t2,t3);
    }
  }
}
/* End of CLooG code */
