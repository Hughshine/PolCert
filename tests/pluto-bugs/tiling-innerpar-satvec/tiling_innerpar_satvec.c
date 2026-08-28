#include <stdio.h>

#define N 16

static int a[N][N];

int main(void) {
  int i, j;

  for (i = 0; i < N; i++) {
    a[i][0] = 1;
    a[0][i] = 1;
  }

#pragma scop
  for (i = 1; i < N; i++)
    for (j = 1; j < N; j++)
      a[i][j] = a[i - 1][j] + a[i][j - 1] + 1;
#pragma endscop

  printf("%d\n", a[N - 1][N - 1]);
  return 0;
}
