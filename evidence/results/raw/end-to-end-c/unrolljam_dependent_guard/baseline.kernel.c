
for (long long i = 1; i < N; ++i) {
  for (long long j = 0; j < M; ++j) {
    A[i][j] = (A[i + -1][j + 1] + 1);
  }
}
