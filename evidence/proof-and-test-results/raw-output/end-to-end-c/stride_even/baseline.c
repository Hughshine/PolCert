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
  
for (long long i = 0; i < N; i += 2) {
  A[i] = (A[i] + i);
}
  printf("%d\n", checksum());
  return 0;
}
