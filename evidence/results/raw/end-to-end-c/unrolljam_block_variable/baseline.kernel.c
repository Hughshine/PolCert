
for (long long i = 0; i < N; ++i) {
  for (long long j = 0; j < M; ++j) {
    A[i][j] = ((A[i][j] + i) + j);
  }
}
