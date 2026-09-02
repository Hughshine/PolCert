#include <math.h>
#define ceild(n,d)  (((n)<0) ? -((-(n))/(d)) : ((n)+(d)-1)/(d))
#define floord(n,d) (((n)<0) ? -((-(n)+(d)-1)/(d)) : (n)/(d))
#define max(x,y)    ((x) > (y)? (x) : (y))
#define min(x,y)    ((x) < (y)? (x) : (y))

#include <stdio.h>

#define I 2
#define H 2
#define J 6
#define K 6

static int a[I][H][J][K];
static int b[I][H][K];

int main(void) {
  int i, h, j, k;

  for (i = 0; i < I; i++) {
    for (h = 0; h < H; h++) {
      a[i][h][0][3] = 10;
      for (k = 0; k < K; k++)
        b[i][h][k] = k + 1;
    }
  }

  int t1, t2, t3, t4, t5, t6, t7, t8, t9;
 register int lbv, ubv;
if ((H >= 1) && (I >= 1) && (J >= 2) && (K >= 1)) {
  for (t2=0;t2<=I-1;t2++) {
    for (t4=0;t4<=H-1;t4++) {
      for (t6=1;t6<=J-1-1;t6+=2) {
        for (t8=0;t8<=K-1;t8++) {
          a[t2][t4][t6][t8] = a[t2][t4][t6 - 1][3] + b[t2][t4][t8];;
          a[t2][t4][(t6+1)][t8] = a[t2][t4][(t6+1) - 1][3] + b[t2][t4][t8];;
        }
      }
      for (;t6<=J-1;t6++) {
        for (t8=0;t8<=K-1;t8++) {
          a[t2][t4][t6][t8] = a[t2][t4][t6 - 1][3] + b[t2][t4][t8];;
        }
      }
    }
  }
}

  printf("%d\n", a[0][0][2][0]);
  return 0;
}
