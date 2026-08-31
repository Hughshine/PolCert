#define S1($i0,$i1)	s = s + a[$i0][$i1];

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if ((M >= 1) && (N >= 1)) {
  for (t2=0;t2<=N-1;t2++) {
    for (t4=0;t4<=M-1;t4++) {
      S1(t2,t4);
    }
  }
}
/* End of CLooG code */
