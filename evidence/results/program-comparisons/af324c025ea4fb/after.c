#include <math.h>
#define ceild(n,d)  (((n)<0) ? -((-(n))/(d)) : ((n)+(d)-1)/(d))
#define floord(n,d) (((n)<0) ? -((-(n)+(d)-1)/(d)) : (n)/(d))
#define max(x,y)    ((x) > (y)? (x) : (y))
#define min(x,y)    ((x) < (y)? (x) : (y))

#include <stdio.h>

#define N 100

static int a[N];
static int b[N];

int main(void) {
  int i;

  int t1, t2, t3;
 register int lbv, ubv;
if (N >= 1) {
  for (t2=0;t2<=N-1;t2++) {
    b[t2] = a[t2];;
  }
  for (t2=0;t2<=N-1;t2++) {
    a[t2] = t2 + 1;;
  }
}

  printf("%d\n", b[N - 1]);
  return 0;
}
