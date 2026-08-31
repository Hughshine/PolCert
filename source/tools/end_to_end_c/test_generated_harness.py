#!/usr/bin/env python3
from __future__ import annotations

from generated_harness import (
    ArrayDim,
    collect_var_ranges,
    div_candidates,
    render_checksum_function,
)


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
    checksum = render_checksum_function(
        {"A": (ArrayDim(0, 1, 0, 2), ArrayDim(0, 2, 0, 3))}, ()
    )
    assert "((__i0) * 3 + __i1)" in checksum, checksum
    print(
        "[generated-harness-unit] PASS expected=import-and-parse-positive-and-negative-ranges "
        "actual=parsed-and-index-weighted interpretation=generated-C-harness-can-start-infer-loop-bounds-and-detect-value-permutations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
