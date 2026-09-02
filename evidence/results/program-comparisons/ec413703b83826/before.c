#include <stdio.h>

#define N 10000

static int a[1][N];

int main(void) {
  int i, j;
  a[0][0] = 1;

#pragma scop
  for (i = 0; i < 1; i++)
    for (j = 1; j < N; j++)
      a[i][j] = a[i][j - 1] + 1;
#pragma endscop

  printf("%d\n", a[0][N - 1]);
  return 0;
}
