#define S1(zT2,zT3,$i0,$i1)	C[$i0][$i1] = 0;
#define S2(zT3,zT4,zT5,$i0,$i1,$i2)	C[$i0][$i1] = C[$i0][$i1] + A[$i0][$i2] * B[$i2][$i1];

		int t1, t2, t3, t4, t5, t6, t7;

	register int lbv, ubv;

/* Start of CLooG code */
if (N >= 1) {
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t3=0;t3<=floord(N-1,32);t3++) {
      for (t4=32*t2;t4<=min(N-1,32*t2+31);t4++) {
        for (t5=32*t3;t5<=min(N-1,32*t3+31);t5++) {
          S1(t2,t3,t4,t5);
        }
      }
    }
  }
  for (t2=0;t2<=floord(N-1,32);t2++) {
    for (t3=0;t3<=floord(N-1,32);t3++) {
      for (t4=0;t4<=floord(N-1,32);t4++) {
        for (t5=32*t2;t5<=(min(N-1,32*t2+31))-3;t5+=4) {
          for (t6=32*t3;t6<=(min(N-1,32*t3+31))-3;t6+=4) {
            for (t7=32*t4;t7<=min(N-1,32*t4+31);t7++) {
              S2(t2,t3,t4,t5,t6,t7);
              S2(t2,t3,t4,(t5+1),t6,t7);
              S2(t2,t3,t4,(t5+2),t6,t7);
              S2(t2,t3,t4,(t5+3),t6,t7);
              S2(t2,t3,t4,t5,(t6+1),t7);
              S2(t2,t3,t4,(t5+1),(t6+1),t7);
              S2(t2,t3,t4,(t5+2),(t6+1),t7);
              S2(t2,t3,t4,(t5+3),(t6+1),t7);
              S2(t2,t3,t4,t5,(t6+2),t7);
              S2(t2,t3,t4,(t5+1),(t6+2),t7);
              S2(t2,t3,t4,(t5+2),(t6+2),t7);
              S2(t2,t3,t4,(t5+3),(t6+2),t7);
              S2(t2,t3,t4,t5,(t6+3),t7);
              S2(t2,t3,t4,(t5+1),(t6+3),t7);
              S2(t2,t3,t4,(t5+2),(t6+3),t7);
              S2(t2,t3,t4,(t5+3),(t6+3),t7);
            }
          }
          for (;t6<=min(N-1,32*t3+31);t6++) {
            for (t7=32*t4;t7<=min(N-1,32*t4+31);t7++) {
              S2(t2,t3,t4,t5,t6,t7);
              S2(t2,t3,t4,(t5+1),t6,t7);
              S2(t2,t3,t4,(t5+2),t6,t7);
              S2(t2,t3,t4,(t5+3),t6,t7);
            }
          }
        }
        for (;t5<=min(N-1,32*t2+31);t5++) {
          for (t6=32*t3;t6<=min(N-1,32*t3+31);t6++) {
            for (t7=32*t4;t7<=min(N-1,32*t4+31);t7++) {
              S2(t2,t3,t4,t5,t6,t7);
            }
          }
        }
      }
    }
  }
}
/* End of CLooG code */
