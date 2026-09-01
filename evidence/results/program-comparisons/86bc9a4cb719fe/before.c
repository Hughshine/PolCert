#define S1(zT1,$i0)	A[2 * $i0] = 1;
#define S2(zT1,$i0)	B[2 * $i0] = A[2 * $i0 + 2];

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=3;t2++) {
  for (t3=32*t2;t3<=min(99,32*t2+31);t3++) {
    S1(t2,t3);
  }
}
for (t2=0;t2<=3;t2++) {
  for (t3=32*t2;t3<=min(99,32*t2+31);t3++) {
    S2(t2,t3);
  }
}
/* End of CLooG code */
