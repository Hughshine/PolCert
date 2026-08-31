#define S1(zT2,zT1,$i0)	a[$i0] = b[$i0];
#define S2(zT2,zT1,$i0)	a[$i0] = b[$i0];

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=floord(N-1,256);t2++) {
  for (t3=8*t2;t3<=min(floord(N-1,32),8*t2+7);t3++) {
    for (t4=32*t3;t4<=min(N-1,32*t3+31);t4++) {
      S1(t2,t3,t4);
    }
  }
}
for (t2=0;t2<=floord(M-1,256);t2++) {
  for (t3=8*t2;t3<=min(floord(M-1,32),8*t2+7);t3++) {
    for (t4=32*t3;t4<=min(M-1,32*t3+31);t4++) {
      S2(t2,t3,t4);
    }
  }
}
/* End of CLooG code */
