#define S1(zT3,zT4,zT5,t,i,j)	u[t][i][j] = u[(t - 1)][i - 1][j] + u[(t - 1)][i][j + 1] + u[(t - 1)][i + 1][j] + u[(t - 1)][i][j - 1];

		int t1, t2, t3, t4, t5, t6;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 2) && (T >= 2)) {
  for (t1=ceild(-N-29,32);t1<=floord(T-2,32);t1++) {
    for (t2=max(t1,-t1-1);t2<=min(min(floord(-16*t1+T-1,16),floord(16*t1+N+14,16)),floord(T+N-2,32));t2++) {
      for (t3=max(max(0,ceild(t1+t2-1,2)),ceild(32*t2-N-29,32));t3<=min(min(floord(T+N-2,32),floord(32*t2+N+29,32)),floord(16*t1+16*t2+N+30,32));t3++) {
        for (t4=max(max(max(max(1,16*t1+16*t2),32*t1+1),32*t2-N+1),32*t3-N+1);t4<=min(min(min(min(T-1,32*t2+30),32*t3+30),16*t1+16*t2+31),32*t1+N+30);t4++) {
          for (t5=max(max(32*t2,t4+1),-32*t1+2*t4-31);t5<=min(min(-32*t1+2*t4,32*t2+31),t4+N-1);t5++) {
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
