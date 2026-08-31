#define S1($i0)	dist_min = 0;
#define S2($i0,$i1)	dist = 0;
#define S3($i0,$i1)	kmin = 0;
#define S4($i0,$i1)	clusterv = 0;

		int t1, t2, t3, t4, t5;

	register int lbv, ubv;

/* Start of CLooG code */
if (pointc >= 1) {
  if ((clusterc >= 1) && (dims >= 1)) {
    for (t2=0;t2<=pointc-1;t2++) {
      S1(t2);
      for (t4=0;t4<=clusterc-1;t4++) {
        S2(t2,t4);
        S3(t2,t4);
      }
      for (t4=0;t4<=dims-1;t4++) {
        S4(t2,t4);
      }
    }
  }
  if ((clusterc >= 1) && (dims <= 0)) {
    for (t2=0;t2<=pointc-1;t2++) {
      S1(t2);
      for (t4=0;t4<=clusterc-1;t4++) {
        S2(t2,t4);
        S3(t2,t4);
      }
    }
  }
  if ((clusterc <= 0) && (dims >= 1)) {
    for (t2=0;t2<=pointc-1;t2++) {
      S1(t2);
      for (t4=0;t4<=dims-1;t4++) {
        S4(t2,t4);
      }
    }
  }
  if ((clusterc <= 0) && (dims <= 0)) {
    for (t2=0;t2<=pointc-1;t2++) {
      S1(t2);
    }
  }
}
/* End of CLooG code */
