#include <stdio.h>

static int A[9];

static int checksum(void) {
  int sum = 0;
  for (int i = 0; i < 9; ++i) {
    sum += A[i] * (i + 3);
  }
  return sum;
}

int main(void) {
  const long long N = 9;
  for (int i = 0; i < 9; ++i) {
    A[i] = i + 1;
  }
  
for (long long i0 = 0; i0 < ((N + 1) / 2); ++i0) {
  A[(2 * i0)] = (A[(2 * i0)] + (2 * i0));
}
  printf("%d\n", checksum());
  return 0;
}
