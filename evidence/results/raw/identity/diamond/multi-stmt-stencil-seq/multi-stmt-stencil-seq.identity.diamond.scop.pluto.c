#define S1(zT1,$i0)	a1[$i0] = a0[$i0 - 1] + a0[$i0] + a0[$i0 + 1];
#define S2(zT1,$i0)	a2[$i0] = a1[$i0 - 1] + a1[$i0] + a1[$i0 + 1];
#define S3(zT1,$i0)	a3[$i0] = a2[$i0 - 1] + a2[$i0] + a2[$i0 + 1];
#define S4(zT1,$i0)	a4[$i0] = a3[$i0 - 1] + a3[$i0] + a3[$i0 + 1];
#define S5(zT1,$i0)	a5[$i0] = a4[$i0 - 1] + a4[$i0] + a4[$i0 + 1];

		int t1, t2, t3, t4;

	register int lbv, ubv;

/* Start of CLooG code */
if (n >= 3) {
  for (t2=0;t2<=floord(n-2,32);t2++) {
    for (t3=max(1,32*t2);t3<=min(n-2,32*t2+31);t3++) {
      S1(t2,t3);
    }
  }
  if (n >= 5) {
    for (t2=0;t2<=floord(n-3,32);t2++) {
      for (t3=max(2,32*t2);t3<=min(n-3,32*t2+31);t3++) {
        S2(t2,t3);
      }
    }
  }
  if (n >= 7) {
    for (t2=0;t2<=floord(n-4,32);t2++) {
      for (t3=max(3,32*t2);t3<=min(n-4,32*t2+31);t3++) {
        S3(t2,t3);
      }
    }
  }
  if (n >= 9) {
    for (t2=0;t2<=floord(n-5,32);t2++) {
      for (t3=max(4,32*t2);t3<=min(n-5,32*t2+31);t3++) {
        S4(t2,t3);
      }
    }
  }
  if (n >= 11) {
    for (t2=0;t2<=floord(n-6,32);t2++) {
      for (t3=max(5,32*t2);t3<=min(n-6,32*t2+31);t3++) {
        S5(t2,t3);
      }
    }
  }
}
/* End of CLooG code */
