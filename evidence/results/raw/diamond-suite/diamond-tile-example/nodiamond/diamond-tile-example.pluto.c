#define S1(zT2,zT3,t,i)	A[t + 1][i] = 0.125 * (A[t][i - 1] + A[t - 2][i + 1]);

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 11) && (T >= 7)) {
  for (t1=0;t1<=floord(T+N-8,32);t1++) {
    for (t2=max(ceild(64*t1-T-29,32),t1);t2<=min(min(floord(T+2*N-14,32),floord(32*t1+N+25,32)),2*t1+1);t2++) {
      for (t3=max(max(max(10,32*t1),16*t2+3),32*t2-N+6);t3<=min(min(min(floord(32*t2+T+29,2),32*t1+31),32*t2+26),T+N-8);t3++) {
        for (t4=max(max(32*t2,t3+5),2*t3-T+2);t4<=min(min(32*t2+31,2*t3-5),t3+N-6);t4++) {
          S1(t1,t2,(2*t3-t4),(-t3+t4));
        }
      }
    }
  }
}
/* End of CLooG code */
