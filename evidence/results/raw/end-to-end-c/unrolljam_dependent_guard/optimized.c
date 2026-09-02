#include <limits.h>
#include <stdlib.h>
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

static long long polcert_z_div(long long numerator, long long denominator) {
  if (denominator == 0) {
    return 0;
  }
  if (numerator == LLONG_MIN && denominator == -1) {
    fputs("PolCert harness: Z.div result exceeds signed 64-bit range\n", stderr);
    abort();
  }
  long long quotient = numerator / denominator;
  long long remainder = numerator % denominator;
  if (remainder != 0 && ((remainder < 0) != (denominator < 0))) {
    quotient -= 1;
  }
  return quotient;
}

static long long polcert_z_mod(long long numerator, long long denominator) {
  if (denominator == 0) {
    return 0;
  }
  if (numerator == LLONG_MIN && denominator == -1) {
    return 0;
  }
  long long remainder = numerator % denominator;
  if (remainder != 0 && ((remainder < 0) != (denominator < 0))) {
    remainder += denominator;
  }
  return remainder;
}

int main(void) {
  init_data();
  
if (1 <= M) {
  if (2 <= N) {
    for (long long i0 = 0; i0 < polcert_z_div(N + -1, 3); ++i0) {
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[3 * i0 + 1][3 * i1] = (A[3 * i0][3 * i1 + 1] + 1);
          A[3 * i0 + 1][3 * i1 + 1] = (A[3 * i0][3 * i1 + 2] + 1);
          A[3 * i0 + 1][3 * i1 + 2] = (A[3 * i0][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[3 * i0 + 1][i1] = (A[3 * i0][i1 + 1] + 1);
        }
      }
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[3 * i0 + 2][3 * i1] = (A[3 * i0 + 1][3 * i1 + 1] + 1);
          A[3 * i0 + 2][3 * i1 + 1] = (A[3 * i0 + 1][3 * i1 + 2] + 1);
          A[3 * i0 + 2][3 * i1 + 2] = (A[3 * i0 + 1][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[3 * i0 + 2][i1] = (A[3 * i0 + 1][i1 + 1] + 1);
        }
      }
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[3 * i0 + 3][3 * i1] = (A[3 * i0 + 2][3 * i1 + 1] + 1);
          A[3 * i0 + 3][3 * i1 + 1] = (A[3 * i0 + 2][3 * i1 + 2] + 1);
          A[3 * i0 + 3][3 * i1 + 2] = (A[3 * i0 + 2][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[3 * i0 + 3][i1] = (A[3 * i0 + 2][i1 + 1] + 1);
        }
      }
    }
    for (long long i0 = 3 * polcert_z_div(N + -1, 3) + 1; i0 < N; ++i0) {
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[i0][3 * i1] = (A[i0 + -1][3 * i1 + 1] + 1);
          A[i0][3 * i1 + 1] = (A[i0 + -1][3 * i1 + 2] + 1);
          A[i0][3 * i1 + 2] = (A[i0 + -1][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[i0][i1] = (A[i0 + -1][i1 + 1] + 1);
        }
      }
    }
  }
}
  printf("%lld\n", checksum());
  return 0;
}
