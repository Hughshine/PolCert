#define S1(zT2,zT3,$i0,$i1)	a[$i0][$i1] = a[$i0 - 1][$i1] + 2;
#define S2(zT2,zT3,$i0,$i1)	a[$i0][$i1] = a[$i0][$i1] + 1;

		int t1, t2, t3, t4, t5, t6, t7, t8;

	register int lbv, ubv;

/* Start of CLooG code */
if (n >= 1) {
  for (t2=ceild(-n-27,32);t2<=floord(n+2,32);t2++) {
    for (t4=ceild(-n-27,32);t4<=floord(n+2,32);t4++) {
      for (t5=max(32*t2,-n+4);t5<=min(n+2,32*t2+31);t5++) {
        for (t7=max(32*t4,-n+4);t7<=min(n+2,32*t4+31);t7++) {
          S1(t2,t4,t5,t7);
        }
      }
    }
  }
  for (t2=ceild(-n-27,32);t2<=floord(n+2,32);t2++) {
    for (t4=ceild(-n-27,32);t4<=floord(n+2,32);t4++) {
      for (t5=max(32*t2,-n+4);t5<=min(n+2,32*t2+31);t5++) {
        for (t7=max(32*t4,-n+4);t7<=min(n+2,32*t4+31);t7++) {
          S2(t2,t4,t5,t7);
        }
      }
    }
  }
}
/* End of CLooG code */
