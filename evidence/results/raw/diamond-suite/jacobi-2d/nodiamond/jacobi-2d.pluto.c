#define S1(zT3,zT4,zT5,t,i,j)	u[t][i][j] = u[(t - 1)][i - 1][j] + u[(t - 1)][i][j + 1] + u[(t - 1)][i + 1][j] + u[(t - 1)][i][j - 1];

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 2) && (T >= 2)) {
  for (t1=0;t1<=floord(T-1,32);t1++) {
    for (t2=t1;t2<=min(floord(T+N-2,32),floord(32*t1+N+30,32));t2++) {
      for (t3=max(ceild(32*t2-N-29,32),t1);t3<=min(min(floord(T+N-2,32),floord(32*t1+N+30,32)),floord(32*t2+N+29,32));t3++) {
        for (t4=max(max(max(1,32*t1),32*t2-N+1),32*t3-N+1);t4<=min(min(min(T-1,32*t1+31),32*t2+30),32*t3+30);t4++) {
          for (t5=max(32*t2,t4+1);t5<=min(32*t2+31,t4+N-1);t5++) {
            for (t6=max(32*t3,t4+1);t6<=min(32*t3+31,t4+N-1);t6++) {
              S1(t1,t2,t3,t4,(-t4+t5),(-t4+t6));
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
