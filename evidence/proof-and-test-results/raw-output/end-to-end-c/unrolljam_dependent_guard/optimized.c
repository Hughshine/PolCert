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
  
if (1 <= M) {
  if (2 <= N) {
    for (long long i0 = 0; i0 < ((N + -1) / 3); ++i0) {
      if (1 <= M) {
        for (long long i1 = 0; i1 < (M / 3); ++i1) {
          A[((3 * i0) + 1)][(3 * i1)] = (A[(3 * i0)][((3 * i1) + 1)] + 1);
          A[((3 * i0) + 1)][((3 * i1) + 1)] = (A[(3 * i0)][((3 * i1) + 2)] + 1);
          A[((3 * i0) + 1)][((3 * i1) + 2)] = (A[(3 * i0)][((3 * i1) + 3)] + 1);
        }
        for (long long i1 = (3 * (M / 3)); i1 < M; ++i1) {
          A[((3 * i0) + 1)][i1] = (A[(3 * i0)][(i1 + 1)] + 1);
        }
      }
      if (1 <= M) {
        for (long long i1 = 0; i1 < (M / 3); ++i1) {
          A[((3 * i0) + 2)][(3 * i1)] = (A[((3 * i0) + 1)][((3 * i1) + 1)] + 1);
          A[((3 * i0) + 2)][((3 * i1) + 1)] = (A[((3 * i0) + 1)][((3 * i1) + 2)] + 1);
          A[((3 * i0) + 2)][((3 * i1) + 2)] = (A[((3 * i0) + 1)][((3 * i1) + 3)] + 1);
        }
        for (long long i1 = (3 * (M / 3)); i1 < M; ++i1) {
          A[((3 * i0) + 2)][i1] = (A[((3 * i0) + 1)][(i1 + 1)] + 1);
        }
      }
      if (1 <= M) {
        for (long long i1 = 0; i1 < (M / 3); ++i1) {
          A[((3 * i0) + 3)][(3 * i1)] = (A[((3 * i0) + 2)][((3 * i1) + 1)] + 1);
          A[((3 * i0) + 3)][((3 * i1) + 1)] = (A[((3 * i0) + 2)][((3 * i1) + 2)] + 1);
          A[((3 * i0) + 3)][((3 * i1) + 2)] = (A[((3 * i0) + 2)][((3 * i1) + 3)] + 1);
        }
        for (long long i1 = (3 * (M / 3)); i1 < M; ++i1) {
          A[((3 * i0) + 3)][i1] = (A[((3 * i0) + 2)][(i1 + 1)] + 1);
        }
      }
    }
    for (long long i0 = ((3 * ((N + -1) / 3)) + 1); i0 < N; ++i0) {
      if (1 <= M) {
        for (long long i1 = 0; i1 < (M / 3); ++i1) {
          A[i0][(3 * i1)] = (A[(i0 + -1)][((3 * i1) + 1)] + 1);
          A[i0][((3 * i1) + 1)] = (A[(i0 + -1)][((3 * i1) + 2)] + 1);
          A[i0][((3 * i1) + 2)] = (A[(i0 + -1)][((3 * i1) + 3)] + 1);
        }
        for (long long i1 = (3 * (M / 3)); i1 < M; ++i1) {
          A[i0][i1] = (A[(i0 + -1)][(i1 + 1)] + 1);
        }
      }
    }
  }
}
  printf("%lld\n", checksum());
  return 0;
}
