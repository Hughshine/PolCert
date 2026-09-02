#!/usr/bin/env python3
from __future__ import annotations

from generated_harness import (
    ArrayDim,
    collect_var_ranges,
    div_candidates,
    render_checksum_function,
)
from loop_to_c import transpile_loop_text
from runner_common import evaluate_outputs


def main() -> int:
    ranges = collect_var_ranges(
        [
            "context(n);\n"
            "for i in range(0, min(n, 8), 2) {\n"
            "  A[i] = i;\n"
            "}\n"
        ],
        {"n": 6},
    )
    assert ranges["i"] == (0, 5), ranges
    descending = collect_var_ranges(
        [
            "context(n);\n"
            "for i in range((n + -1), -1, -2) {\n"
            "  A[i] = i;\n"
            "}\n"
        ],
        {"n": 6},
    )
    assert descending["i"] == (0, 5), descending
    assert div_candidates(-5, -5, 2, 2) == (-3, -3)
    lowered = transpile_loop_text(
        "context(N);\n"
        "for i in range(((-1 * N) / 32), ((N + 31) / 32)) {\n"
        "  if (((i % 2) == 0 && ((-1 * i) / 2) <= 0)) {\n"
        "    A[(((-1 * i) + 1) / 2)] = (B[i] / beta);\n"
        "  }\n"
        "}\n"
        "innermost parallel for j in range(0, N) {\n"
        "  A[j] = B[j];\n"
        "}\n"
    )
    assert "polcert_z_div(-1 * N, 32)" in lowered, lowered
    assert "polcert_z_mod(i, 2)" in lowered, lowered
    assert "polcert_z_div(-1 * i, 2)" in lowered, lowered
    assert "A[polcert_z_div(-1 * i + 1, 2)]" in lowered, lowered
    assert "B[i] / beta" in lowered, lowered
    assert "#pragma omp simd" in lowered, lowered
    nonfinite = evaluate_outputs(
        "nan\n", "nan\n", abs_tolerance=1e-9, rel_tolerance=1e-9
    )
    assert nonfinite["exact_match"]
    assert not nonfinite["numeric_finite"]
    assert not nonfinite["outputs_match"]
    checksum = render_checksum_function(
        {"A": (ArrayDim(0, 1, 0, 2), ArrayDim(0, 2, 0, 3))}, ()
    )
    assert "((__i0) * 3 + __i1)" in checksum, checksum
    print(
        "[generated-harness-unit] PASS expected=range-checks-and-Rocq-Z-integer-operators "
        "actual=parsed-index-weighted-and-semantics-lowered "
        "interpretation=generated-C-harness-matches-Loop-control-arithmetic"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
