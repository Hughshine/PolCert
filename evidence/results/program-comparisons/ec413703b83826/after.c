#include <omp.h>
#include <math.h>
#define ceild(n,d)  (((n)<0) ? -((-(n))/(d)) : ((n)+(d)-1)/(d))
#define floord(n,d) (((n)<0) ? -((-(n)+(d)-1)/(d)) : (n)/(d))
#define max(x,y)    ((x) > (y)? (x) : (y))
#define min(x,y)    ((x) < (y)? (x) : (y))

#include <stdio.h>

#define N 10000

static int a[1][N];

int main(void) {
  int i, j;
  a[0][0] = 1;

  int t1, t2;
 int lb, ub, lbp, ubp, lb2, ub2;
 register int lbv, ubv;
if (N >= 2) {
  lbp=1;
  ubp=N-1;
#pragma omp parallel for private(lbv,ubv)
  for (t2=lbp;t2<=ubp;t2++) {
    a[0][t2] = a[0][t2 - 1] + 1;;
  }
}

  printf("%d\n", a[0][N - 1]);
  return 0;
}
