#include <stdio.h>

#define N 100

static int a[N];
static int b[N];

int main(void) {
  int i;

#pragma scop
  for (i = 0; i < N; i++) {
    a[i] = i + 1;
    b[i] = a[i];
  }
#pragma endscop

  printf("%d\n", b[N - 1]);
  return 0;
}
