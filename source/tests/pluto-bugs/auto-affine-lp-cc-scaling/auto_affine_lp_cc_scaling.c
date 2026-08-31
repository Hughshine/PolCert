#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

#define N 40

static uint64_t x[N][N];
static uint64_t y[N][N];
static uint64_t c[N][N];
static uint64_t d[N][N];

int main(void) {
  int i;
  int j;

  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      x[i][j] = 1;
      y[i][j] = 2;
    }
  }

#pragma scop
  for (i = 1; i < N - 1; i++) {
    for (j = 2; j < N - 2; j++) {
      c[i][j] = x[i - 1][j + 1] + x[i][j - 1];
      d[i][j] = y[i - 1][j + 1] + y[i][j - 2];
      x[i][j] = 1000 * i + j + 3;
      y[i][j] = 2000 * i + j + 5;
    }
  }
#pragma endscop

  uint64_t checksum = 0;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      checksum = checksum * 131 + c[i][j] * 17 + d[i][j];
    }
  }
  printf("%" PRIu64 "\n", checksum);
  return 0;
}
