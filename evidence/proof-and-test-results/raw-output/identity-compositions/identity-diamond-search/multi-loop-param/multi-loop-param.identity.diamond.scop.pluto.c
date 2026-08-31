#define S1(zT1,$i0)	a[$i0] = b[$i0];
#define S2(zT1,$i0)	a[$i0] = b[$i0];
#define S3(zT1,$i0)	a[$i0] = b[$i0];

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=floord(N-1,32);t2++) {
  for (t3=32*t2;t3<=min(N-1,32*t2+31);t3++) {
    S1(t2,t3);
  }
}
for (t2=0;t2<=floord(M-1,32);t2++) {
  for (t3=32*t2;t3<=min(M-1,32*t2+31);t3++) {
    S2(t2,t3);
  }
}
for (t2=0;t2<=floord(L-1,32);t2++) {
  for (t3=32*t2;t3<=min(L-1,32*t2+31);t3++) {
    S3(t2,t3);
  }
}
/* End of CLooG code */
