// CHECK: T(S1): (i, j, k)
// TILE-PARALLEL: T(S1): (i/32, j/32, k/32, i, j, k)
// READSCOP-MATMUL: ===DIRECT-LOG===
// READSCOP-MATMUL-NOT: number of columns too small
// READSCOP-MATMUL: [pluto] Number of deps: 6
// READSCOP-MATMUL: [Pluto] After tile scheduling:
// READSCOP-MATMUL: ===STAGE2-LOG===
// READSCOP-MATMUL-NOT: number of columns too small
// READSCOP-MATMUL: [pluto] Number of deps: 6
// READSCOP-MATMUL: [Pluto] After tile scheduling:
// READSCOP-MATMUL: ===DIRECT-SCOP===
// READSCOP-MATMUL: # Iterator name
// READSCOP-MATMUL: t2
// READSCOP-MATMUL: ===STAGE2-SCOP===
// READSCOP-MATMUL: # Iterator name
// READSCOP-MATMUL: t2
// READSCOP-MATMUL: ===DIRECT-CODE===
// READSCOP-MATMUL: #pragma omp parallel for
// READSCOP-MATMUL: for (t2=lbp;t2<=ubp;t2++) {
// READSCOP-MATMUL: ===STAGE2-CODE===
// READSCOP-MATMUL: #pragma omp parallel for
// READSCOP-MATMUL: for (t2=lbp;t2<=ubp;t2++) {

#define M 2048
#define N 2048
#define K 2048

double A[M][K + 13];
double B[K][N + 13];
double C[M][N + 13];

int main() {
  int i, j, k;
  register double s;

#pragma scop
  for (i = 0; i < M; i++)
    for (j = 0; j < N; j++)
      for (k = 0; k < K; k++)
        C[i][j] = C[i][j] + A[i][k] * B[k][j];
#pragma endscop

  return 0;
}
