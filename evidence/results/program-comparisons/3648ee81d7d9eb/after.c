#include <omp.h>
#include <math.h>
#define ceild(n,d)  (((n)<0) ? -((-(n))/(d)) : ((n)+(d)-1)/(d))
#define floord(n,d) (((n)<0) ? -((-(n)+(d)-1)/(d)) : (n)/(d))
#define max(x,y)    ((x) > (y)? (x) : (y))
#define min(x,y)    ((x) < (y)? (x) : (y))

#include <stdio.h>

#define N 16

static int a[N][N];

int main(void) {
  int i, j;

  for (i = 0; i < N; i++) {
    a[i][0] = 1;
    a[0][i] = 1;
  }

  int t1, t2, t3, t4, t5, t6, t7, t8;
 int lb, ub, lbp, ubp, lb2, ub2;
 register int lbv, ubv;
if (N >= 2) {
  for (t2=0;t2<=floord(N-1,2);t2++) {
    lbp=0;
    ubp=floord(N-1,2);
#pragma omp parallel for private(lbv,ubv,t5,t6,t7,t8)
    for (t4=lbp;t4<=ubp;t4++) {
      for (t5=max(1,2*t2);t5<=min(N-1,2*t2+1);t5++) {
        for (t7=max(1,2*t4);t7<=min(N-1,2*t4+1);t7++) {
          a[t5][t7] = a[t5 - 1][t7] + a[t5][t7 - 1] + 1;;
        }
      }
    }
  }
}

  printf("%d\n", a[N - 1][N - 1]);
  return 0;
}
