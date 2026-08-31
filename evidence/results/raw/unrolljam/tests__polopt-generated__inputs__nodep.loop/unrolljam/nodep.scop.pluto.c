#define S1(zT2,zT3,$i0,$i1)	A[4 * $i0 + $i1] = 2 * A[4 * $i0 + $i1] + 2;

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
for (t1=0;t1<=3;t1++) {
  for (t3=32*t1;t3<=min(99,32*t1+31);t3++) {
    for (t4=0;t4<=3;t4++) {
      S1(t1,0,t3,t4);
    }
  }
}
/* End of CLooG code */
