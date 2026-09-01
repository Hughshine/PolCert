#define S1($i0,$i1)	a[$i0][$i1] = b[$i0][$i1 - 1] + a[$i0][$i1 - 1];
#define S2($i0,$i1)	b[$i0][$i1] = a[$i0 - 1][$i1 + 1] + b[$i0 - 1][$i1];

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if (n >= 1) {
  for (t2=0;t2<=n-1;t2++) {
    for (t4=0;t4<=n-1;t4++) {
      S1(t2,t4);
      S2(t2,t4);
    }
  }
}
/* End of CLooG code */
