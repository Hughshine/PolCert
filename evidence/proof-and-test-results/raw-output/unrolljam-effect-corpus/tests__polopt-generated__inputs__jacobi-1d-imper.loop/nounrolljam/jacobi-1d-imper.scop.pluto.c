#define S1(zT2,zT3,$i0,$i1)	b[$i1] = 0.33333 * a[$i1 - 1] + a[$i1] + a[$i1 + 1];
#define S2(zT2,zT3,$i0,$i1)	a[$i1] = b[$i1];

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 4) && (T >= 1)) {
  for (t1=0;t1<=floord(T-1,32);t1++) {
    for (t2=2*t1;t2<=min(floord(2*T+N-3,32),floord(64*t1+N+61,32));t2++) {
      if (t1 <= floord(32*t2-N+1,64)) {
        if ((N+1)%2 == 0) {
          S2(t1,t2,((32*t2-N+1)/2),(N-2));
        }
      }
      if (N == 4) {
        for (t3=max(32*t1,16*t2-1);t3<=min(min(T-1,32*t1+31),16*t2+14);t3++) {
          S1(t1,t2,t3,2);
          S2(t1,t2,t3,2);
        }
      }
      for (t3=max(ceild(32*t2-N+2,2),32*t1);t3<=min(min(min(floord(32*t2-N+32,2),T-1),32*t1+31),16*t2-2);t3++) {
        for (t4=32*t2;t4<=2*t3+N-2;t4++) {
          S1(t1,t2,t3,(-2*t3+t4));
          S2(t1,t2,t3,(-2*t3+t4-1));
        }
        S2(t1,t2,t3,(N-2));
      }
      for (t3=max(ceild(32*t2-N+33,2),32*t1);t3<=min(min(T-1,32*t1+31),16*t2-2);t3++) {
        for (t4=32*t2;t4<=32*t2+31;t4++) {
          S1(t1,t2,t3,(-2*t3+t4));
          S2(t1,t2,t3,(-2*t3+t4-1));
        }
      }
      if (N >= 5) {
        for (t3=max(32*t1,16*t2-1);t3<=min(min(floord(32*t2-N+32,2),T-1),32*t1+31);t3++) {
          S1(t1,t2,t3,2);
          for (t4=2*t3+3;t4<=2*t3+N-2;t4++) {
            S1(t1,t2,t3,(-2*t3+t4));
            S2(t1,t2,t3,(-2*t3+t4-1));
          }
          S2(t1,t2,t3,(N-2));
        }
      }
      for (t3=max(max(ceild(32*t2-N+33,2),32*t1),16*t2-1);t3<=min(min(T-1,32*t1+31),16*t2+14);t3++) {
        S1(t1,t2,t3,2);
        for (t4=2*t3+3;t4<=32*t2+31;t4++) {
          S1(t1,t2,t3,(-2*t3+t4));
          S2(t1,t2,t3,(-2*t3+t4-1));
        }
      }
    }
  }
}
/* End of CLooG code */
