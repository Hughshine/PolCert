#define S1($i0,$i1)	a[$i0] = 0;
#define S2($i0,$i1)	a[$i1] = 0;

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=N-1;t2++) {
    for (t4=0;t4<=N-1;t4++) {
      S1(t2,t4);
      S2(t2,t4);
    }
  }
}
/* End of CLooG code */
