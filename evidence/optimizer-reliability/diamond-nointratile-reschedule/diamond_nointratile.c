#include <stdio.h>

#define TMAX 2
#define NX 2
#define NY 3

static int ex[NX][NY + 1];
static int ey[NX + 1][NY];
static int hz[NX][NY];

int main(void) {
  int t, i, j;

  for (i = 0; i < NX; ++i) {
    for (j = 0; j < NY; ++j) {
      ex[i][j] = 3 * i - j;
      ey[i][j] = i + 2 * j;
      hz[i][j] = 4 * i + j;
    }
  }

#pragma scop
  for (t = 0; t < TMAX; ++t) {
    for (j = 0; j < NY; ++j)
      ey[0][j] = t;
    for (i = 1; i < NX; ++i)
      for (j = 0; j < NY; ++j)
        ey[i][j] -= hz[i][j] - hz[i - 1][j];
    for (i = 0; i < NX; ++i)
      for (j = 1; j < NY; ++j)
        ex[i][j] -= hz[i][j] - hz[i][j - 1];
    for (i = 0; i < NX; ++i)
      for (j = 0; j < NY; ++j)
        hz[i][j] -=
            ex[i][j + 1] - ex[i][j] + ey[i + 1][j] - ey[i][j];
  }
#pragma endscop

  long long sum = 0;
  for (i = 0; i < NX; ++i)
    for (j = 0; j < NY; ++j)
      sum += ex[i][j] + ey[i][j] + hz[i][j];
  printf("%lld\n", sum);
  return 0;
}
