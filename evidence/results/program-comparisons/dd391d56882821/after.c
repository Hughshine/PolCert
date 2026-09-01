#define S1($i0,$i1,$i2)	a[$i1][$i2] = a[$i1 - 1][$i2 - 1] + a[$i1 - 1][$i2] + a[$i1 - 1][$i2 + 1] + a[$i1][$i2 - 1] + a[$i1][$i2] + a[$i1][$i2 + 1] + a[$i1 + 1][$i2 - 1] + a[$i1 + 1][$i2] + a[$i1 + 1][$i2 + 1] / 9.0;

		int t1, t2, t3, t4, t5, t6, t7;

	register int lbv, ubv;

/* Start of CLooG code */
if ((N >= 3) && (T >= 1)) {
  for (t2=0;t2<=T-1;t2++) {
    for (t4=1;t4<=N-2;t4++) {
      for (t6=1;t6<=N-2;t6++) {
        S1(t2,t4,t6);
      }
    }
  }
}
/* End of CLooG code */
