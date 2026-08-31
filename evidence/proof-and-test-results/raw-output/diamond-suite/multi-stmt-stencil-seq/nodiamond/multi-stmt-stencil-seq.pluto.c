#define S1(i)	a1[i] = a0[i - 1] + a0[i] + a0[i + 1];
#define S2(i)	a2[i] = a1[i - 1] + a1[i] + a1[i + 1];
#define S3(i)	a3[i] = a2[i - 1] + a2[i] + a2[i + 1];
#define S4(i)	a4[i] = a3[i - 1] + a3[i] + a3[i + 1];
#define S5(i)	a5[i] = a4[i - 1] + a4[i] + a4[i + 1];

		int t1, t2;

	register int lbv, ubv;

/* Start of CLooG code */
if (n >= 3) {
  for (t1=1;t1<=min(2,n-2);t1++) {
    S1(t1);
  }
  for (t1=3;t1<=min(4,n-2);t1++) {
    S1(t1);
    S2((t1-1));
  }
  for (t1=5;t1<=min(6,n-2);t1++) {
    S1(t1);
    S2((t1-1));
    S3((t1-2));
  }
  for (t1=7;t1<=min(8,n-2);t1++) {
    S1(t1);
    S2((t1-1));
    S3((t1-2));
    S4((t1-3));
  }
  for (t1=9;t1<=n-2;t1++) {
    S1(t1);
    S2((t1-1));
    S3((t1-2));
    S4((t1-3));
    S5((t1-4));
  }
}
/* End of CLooG code */
