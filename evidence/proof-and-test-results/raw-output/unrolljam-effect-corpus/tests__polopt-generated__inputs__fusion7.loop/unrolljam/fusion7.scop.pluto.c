#define S1(zT1,$i0)	a[$i0] = b[$i0];
#define S2(zT1,$i0)	a[$i0] = b[$i0];

		int t1, t2, t3;

	register int lbv, ubv;

/* Start of CLooG code */
if ((M >= 0) && (N >= 0)) {
  for (t1=0;t1<=floord(N+M-1,32);t1++) {
    for (t2=32*t1;t2<=min(min(M-1,N-1),32*t1+31);t2++) {
      S1(t1,t2);
      S2(t1,t2);
    }
    for (t2=max(M,32*t1);t2<=min(N-1,32*t1+31);t2++) {
      S1(t1,t2);
    }
    for (t2=max(N,32*t1);t2<=min(M-1,32*t1+31);t2++) {
      S2(t1,t2);
    }
  }
}
if (M <= -1) {
  for (t1=0;t1<=floord(N-1,32);t1++) {
    for (t2=32*t1;t2<=min(N-1,32*t1+31);t2++) {
      S1(t1,t2);
    }
  }
}
if (N <= -1) {
  for (t1=0;t1<=floord(M-1,32);t1++) {
    for (t2=32*t1;t2<=min(M-1,32*t1+31);t2++) {
      S2(t1,t2);
    }
  }
}
/* End of CLooG code */
