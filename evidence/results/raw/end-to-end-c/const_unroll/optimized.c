#include <stdio.h>

static int A[4];

static int checksum(void) {
  int sum = 0;
  for (int i = 0; i < 4; ++i) {
    sum += A[i] * (i + 1);
  }
  return sum;
}

int main(void) {
  for (int i = 0; i < 4; ++i) {
    A[i] = 0;
  }
  A[0] = 1;
A[1] = 2;
A[2] = 3;
A[3] = 4;
  printf("%d\n", checksum());
  return 0;
}
