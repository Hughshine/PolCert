#define S1(zT2,zT3,$i0,$i1)	e[$i1] = e[$i1] - coeff1 * h[$i1] - h[$i1 - 1];
#define S2(zT2,zT3,$i0,$i1)	h[$i1] = h[$i1] - coeff2 * e[$i1 + 1] - e[$i1];

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 1) && (T >= 1)) {
  for (t1=0;t1<=floord(T,32);t1++) {
    for (t2=t1;t2<=min(floord(T+N,32),floord(32*t1+N+31,32));t2++) {
      if ((N >= 2) && (t1 <= floord(32*t2-N,32)) && (t2 >= ceild(N+1,32))) {
        S2(t1,t2,(32*t2-N),(N-1));
      }
      if (N == 1) {
        for (t3=max(max(1,32*t1),32*t2-1);t3<=(min(min(T,32*t1+31),32*t2+30))-3;t3+=4) {
          S2(t1,t2,t3,0);
          S2(t1,t2,(t3+1),0);
          S2(t1,t2,(t3+2),0);
          S2(t1,t2,(t3+3),0);
        }
        for (;t3<=min(min(T,32*t1+31),32*t2+30);t3++) {
          S2(t1,t2,t3,0);
        }
      }
      if (N >= 2) {
        for (t3=max(max(1,32*t1),32*t2-N+1);t3<=min(min(T,32*t1+31),32*t2-N+31);t3++) {
          for (t4=max(32*t2,t3+1);t4<=t3+N-1;t4++) {
            S1(t1,t2,t3,(-t3+t4));
            S2(t1,t2,t3,(-t3+t4-1));
          }
          S2(t1,t2,t3,(N-1));
        }
      }
      for (t3=max(max(1,32*t1),32*t2-N+32);t3<=min(min(T,32*t1+31),32*t2+30);t3++) {
        for (t4=max(32*t2,t3+1);t4<=32*t2+31;t4++) {
          S1(t1,t2,t3,(-t3+t4));
          S2(t1,t2,t3,(-t3+t4-1));
        }
      }
    }
  }
}
/* End of CLooG code */
