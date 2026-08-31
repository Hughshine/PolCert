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

#pragma scop
  for (i = 0; i < I; i++)
    for (h = 0; h < H; h++)
      for (j = 1; j < J; j++)
        for (k = 0; k < K; k++)
          a[i][h][j][k] = a[i][h][j - 1][3] + b[i][h][k];
#pragma endscop

  printf("%d\n", a[0][0][2][0]);
  return 0;
}
