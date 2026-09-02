
if (1 <= M) {
  if (2 <= N) {
    for (long long i0 = 0; i0 < polcert_z_div(N + -1, 3); ++i0) {
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[3 * i0 + 1][3 * i1] = (A[3 * i0][3 * i1 + 1] + 1);
          A[3 * i0 + 1][3 * i1 + 1] = (A[3 * i0][3 * i1 + 2] + 1);
          A[3 * i0 + 1][3 * i1 + 2] = (A[3 * i0][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[3 * i0 + 1][i1] = (A[3 * i0][i1 + 1] + 1);
        }
      }
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[3 * i0 + 2][3 * i1] = (A[3 * i0 + 1][3 * i1 + 1] + 1);
          A[3 * i0 + 2][3 * i1 + 1] = (A[3 * i0 + 1][3 * i1 + 2] + 1);
          A[3 * i0 + 2][3 * i1 + 2] = (A[3 * i0 + 1][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[3 * i0 + 2][i1] = (A[3 * i0 + 1][i1 + 1] + 1);
        }
      }
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[3 * i0 + 3][3 * i1] = (A[3 * i0 + 2][3 * i1 + 1] + 1);
          A[3 * i0 + 3][3 * i1 + 1] = (A[3 * i0 + 2][3 * i1 + 2] + 1);
          A[3 * i0 + 3][3 * i1 + 2] = (A[3 * i0 + 2][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[3 * i0 + 3][i1] = (A[3 * i0 + 2][i1 + 1] + 1);
        }
      }
    }
    for (long long i0 = 3 * polcert_z_div(N + -1, 3) + 1; i0 < N; ++i0) {
      if (1 <= M) {
        for (long long i1 = 0; i1 < polcert_z_div(M, 3); ++i1) {
          A[i0][3 * i1] = (A[i0 + -1][3 * i1 + 1] + 1);
          A[i0][3 * i1 + 1] = (A[i0 + -1][3 * i1 + 2] + 1);
          A[i0][3 * i1 + 2] = (A[i0 + -1][3 * i1 + 3] + 1);
        }
        for (long long i1 = 3 * polcert_z_div(M, 3); i1 < M; ++i1) {
          A[i0][i1] = (A[i0 + -1][i1 + 1] + 1);
        }
      }
    }
  }
}
