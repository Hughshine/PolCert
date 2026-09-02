#include <limits.h>
#include <stdlib.h>
#include <stdio.h>

#define N 10
#define M 7

static long long A[N][M];

static void init_data(void) {
  for (long long i = 0; i < N; ++i) {
    for (long long j = 0; j < M; ++j) {
      A[i][j] = (i * 101) + (j * 17) + 3;
    }
  }
}

static long long checksum(void) {
  long long sum = 0;
  for (long long i = 0; i < N; ++i) {
    for (long long j = 0; j < M; ++j) {
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
  
for (long long i = 0; i < N; ++i) {
  for (long long j = 0; j < M; ++j) {
    A[i][j] = ((A[i][j] + i) + j);
  }
}
  printf("%lld\n", checksum());
  return 0;
}
