#include <limits.h>
#include <stdlib.h>
#include <stdio.h>

static int A[9];

static int checksum(void) {
  int sum = 0;
  for (int i = 0; i < 9; ++i) {
    sum += A[i] * (i + 3);
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
  const long long N = 9;
  for (int i = 0; i < 9; ++i) {
    A[i] = i + 1;
  }
  
for (long long i = 0; i < N; i += 2) {
  A[i] = (A[i] + i);
}
  printf("%d\n", checksum());
  return 0;
}
