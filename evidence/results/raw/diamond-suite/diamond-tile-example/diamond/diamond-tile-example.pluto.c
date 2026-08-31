#define S1(zT2,zT3,t,i)	A[t + 1][i] = 0.125 * (A[t][i - 1] + A[t - 2][i + 1]);

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 11) && (T >= 7)) {
  for (t1=0;t1<=floord(T+N-8,32);t1++) {
    for (t2=max(max(ceild(16*t1-N-9,16),ceild(-N-20,32)),-t1-1);t2<=min(min(floord(-16*t1+T-2,16),floord(T-7,32)),t1);t2++) {
      for (t3=max(max(32*t1,-32*t2-21),32*t2+10);t3<=min(min(min(32*t1+31,T+N-8),-32*t2+2*T-4),32*t2+2*N+19);t3++) {
        for (t4=max(max(ceild(-32*t2+3*t3-31,2),t3+5),2*t3-T+2);t4<=min(min(floord(-32*t2+3*t3,2),2*t3-5),t3+N-6);t4++) {
          S1(t1,t2,(2*t3-t4),(-t3+t4));
        }
      }
    }
  }
}
/* End of CLooG code */
