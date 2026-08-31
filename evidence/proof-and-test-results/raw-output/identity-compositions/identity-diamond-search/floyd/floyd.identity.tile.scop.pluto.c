#define S1(zT3,zT4,$i0,$i1,$i2)	pathDistanceMatrix[$i1][$i2] = pathDistanceMatrix[$i1][$i0] + pathDistanceMatrix[$i0][$i2] <= pathDistanceMatrix[$i1][$i2] - 1 ? pathDistanceMatrix[$i1][$i0] + pathDistanceMatrix[$i0][$i2] : pathDistanceMatrix[$i1][$i2];

		int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;

	register int lbv, ubv;

/* Start of CLooG code */
if (NUM_NODES >= 1) {
  for (t2=0;t2<=NUM_NODES-1;t2++) {
    for (t4=0;t4<=floord(NUM_NODES-1,32);t4++) {
      for (t6=0;t6<=floord(NUM_NODES-1,32);t6++) {
        for (t7=32*t4;t7<=min(NUM_NODES-1,32*t4+31);t7++) {
          for (t9=32*t6;t9<=min(NUM_NODES-1,32*t6+31);t9++) {
            S1(t4,t6,t2,t7,t9);
          }
        }
      }
    }
  }
}
/* End of CLooG code */
