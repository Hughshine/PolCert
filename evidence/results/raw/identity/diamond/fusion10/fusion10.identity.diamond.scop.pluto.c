#define S1(zT2,zT3,$i0,$i1)	A[2 * $i0 + $i1] = 1;
#define S2(zT2,zT3,$i0,$i1)	B[2 * $i0 + $i1] = A[2 * $i0 + $i1];

		int t1, t2, t3, t4, t5, t6, t7, t8;

	register int lbv, ubv;

/* Start of CLooG code */
for (t5=0;t5<=1;t5++) {
  for (t7=0;t7<=1;t7++) {
    S1(0,0,t5,t7);
  }
}
for (t5=0;t5<=1;t5++) {
  for (t7=0;t7<=1;t7++) {
    S2(0,0,t5,t7);
  }
}
/* End of CLooG code */
