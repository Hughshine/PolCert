#define S1($i0)	autocorr = autocorr + 1;
#define S2($i0)	temp3 = temp3 + 1;

		int t1, t2, t3;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=N-1;t2++) {
  S1(t2);
}
for (t2=0;t2<=M-1;t2++) {
  S2(t2);
}
/* End of CLooG code */
