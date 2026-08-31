#define S1(zT1,$i0)	c[$i0] = $i0;
#define S2(zT1,$i0)	b[$i0] = $i0;

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
for (t3=0;t3<=1;t3++) {
  S1(0,t3);
}
for (t2=0;t2<=floord(N-1,32);t2++) {
  for (t3=32*t2;t3<=min(N-1,32*t2+31);t3++) {
    S2(t2,t3);
  }
}
/* End of CLooG code */
