#include <stdio.h>

static int A[9];

static int checksum(void) {
  int sum = 0;
  for (int i = 0; i < 9; ++i) {
    sum += A[i] * (i + 5);
  }
  return sum;
}

int main(void) {
  const long long N = 9;
  for (int i = 0; i < 9; ++i) {
    A[i] = i + 2;
  }
  
for (long long i = N - 1; i > -1; i += -2) {
  A[i] = (i + 7);
}
  printf("%d\n", checksum());
  return 0;
}
