#define S1(zT1,$i0)	x[$i0] = a[$i0] + b[$i0];
#define S2()	s = 0.0;
#define S3($i0)	s = s + x[$i0] * 3;

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=floord(N-1,32);t2++) {
  for (t3=32*t2;t3<=min(N-1,32*t2+31);t3++) {
    S1(t2,t3);
  }
}
S2();
for (t2=0;t2<=N-1;t2++) {
  S3(t2);
}
/* End of CLooG code */
