#define S1(zT2,zT3,$i0,$i1)	B[$i0][$i1] = $i1 + $i0;
#define S2(zT2,zT3,$i0,$i1)	C[$i1][$i0] = B[$i1 - 1][$i0 - 1] + B[$i1][$i0];

		int t1, t2, t3, t4, t5, t6, t7, t8;

	register int lbv, ubv;

/* Start of CLooG code */
for (t2=0;t2<=312;t2++) {
  for (t4=0;t4<=312;t4++) {
    for (t5=32*t2;t5<=min(9999,32*t2+31);t5++) {
      for (t7=32*t4;t7<=min(9999,32*t4+31);t7++) {
        S1(t2,t4,t5,t7);
      }
    }
  }
}
for (t2=0;t2<=312;t2++) {
  for (t4=0;t4<=312;t4++) {
    for (t5=32*t2;t5<=min(9999,32*t2+31);t5++) {
      for (t7=32*t4;t7<=min(9999,32*t4+31);t7++) {
        S2(t2,t4,t5,t7);
      }
    }
  }
}
/* End of CLooG code */
