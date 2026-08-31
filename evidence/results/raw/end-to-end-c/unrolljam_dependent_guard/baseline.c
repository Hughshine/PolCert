#include <stdio.h>

#define N 10
#define M 7

static long long A[N][M + 1];

static void init_data(void) {
  for (long long i = 0; i < N; ++i) {
    for (long long j = 0; j < M + 1; ++j) {
      A[i][j] = (i * 101) + (j * 17) + 3;
    }
  }
}

static long long checksum(void) {
  long long sum = 0;
  for (long long i = 0; i < N; ++i) {
    for (long long j = 0; j < M + 1; ++j) {
      sum += A[i][j] * (i + 1) * (j + 3);
    }
  }
  return sum;
}

int main(void) {
  init_data();
  
for (long long i = 1; i < N; ++i) {
  for (long long j = 0; j < M; ++j) {
    A[i][j] = (A[(i + -1)][(j + 1)] + 1);
  }
}
  printf("%lld\n", checksum());
  return 0;
}
