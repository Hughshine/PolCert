#define S1(zT1,$i0)	c[$i0] = 0;
#define S2(zT2,$i0,$i1)	c[$i0 + $i1] = c[$i0 + $i1] + a[$i0] * b[$i1];

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if (n >= 1) {
  for (t2=0;t2<=floord(n-1,16);t2++) {
    for (t3=32*t2;t3<=min(2*n-1,32*t2+31);t3++) {
      S1(t2,t3);
    }
  }
  for (t2=0;t2<=n-1;t2++) {
    for (t4=0;t4<=floord(n-1,32);t4++) {
      for (t5=32*t4;t5<=min(n-1,32*t4+31);t5++) {
        S2(t4,t2,t5);
      }
    }
  }
}
/* End of CLooG code */
