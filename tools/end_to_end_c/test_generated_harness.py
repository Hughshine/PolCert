#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import pathlib
import struct
import subprocess
import tempfile

from generated_harness import (
    ArrayDim,
    STATE_DIGEST_HELPERS_C,
    collect_var_ranges,
    div_candidates,
    render_checksum_function,
    render_state_digest_function,
)
from loop_to_c import INTEGER_HELPERS_C, transpile_loop_text
from runner_common import evaluate_outputs, evaluate_state_digest_outputs


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
    mixed_nonfinite = evaluate_outputs(
        "checksum=inf\n", "checksum=inf\n", abs_tolerance=1e-9, rel_tolerance=1e-9
    )
    assert not mixed_nonfinite["outputs_match"]
    empty = evaluate_outputs("", "", abs_tolerance=1e-9, rel_tolerance=1e-9)
    assert not empty["outputs_match"]
    with tempfile.TemporaryDirectory(prefix="polcert-z-arithmetic-") as temporary:
        source = pathlib.Path(temporary) / "z_arithmetic.c"
        executable = pathlib.Path(temporary) / "z_arithmetic"
        source.write_text(
            "#include <limits.h>\n#include <math.h>\n#include <stdio.h>\n"
            "#include <stdlib.h>\n#include <string.h>\n"
            + INTEGER_HELPERS_C
            + STATE_DIGEST_HELPERS_C
            + "int main(void) {\n"
            + "  polcert_sha256_ctx ctx; unsigned char digest[32]; unsigned int i;\n"
            + "  unsigned long long count = 0; polcert_sha256_init(&ctx);\n"
            + '  printf("%lld %lld %lld %lld %lld %lld\\n",\n'
            + "    polcert_z_div(3, -2), polcert_z_mod(3, -2),\n"
            + "    polcert_z_div(-3, -2), polcert_z_mod(-3, -2),\n"
            + "    polcert_z_div(3, 0), polcert_z_mod(3, 0));\n"
            + "  polcert_observe_double(&ctx, &count, 1.0);\n"
            + "  polcert_observe_double(&ctx, &count, -2.5);\n"
            + "  polcert_sha256_final(&ctx, digest);\n"
            + '  printf("observed_value_count=%llu\\nstate_sha256=", count);\n'
            + '  for (i = 0; i < 32; ++i) printf("%02x", digest[i]);\n'
            + "  putchar('\\n');\n"
            + "  return 0;\n}\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["cc", "-std=c99", str(source), "-o", str(executable)], check=True
        )
        observed = subprocess.run(
            [str(executable)], text=True, capture_output=True, check=True
        ).stdout
        expected_digest = hashlib.sha256(
            struct.pack("<d", 1.0) + struct.pack("<d", -2.5)
        ).hexdigest()
        assert observed == (
            "-2 -1 1 -1 0 0\n"
            f"observed_value_count=2\nstate_sha256={expected_digest}\n"
        ), observed
        digest_result = evaluate_state_digest_outputs(
            observed.split("\n", 1)[1], observed.split("\n", 1)[1]
        )
        assert digest_result["outputs_match"]
        assert digest_result["numeric_value_count"] == 2
    checksum = render_checksum_function(
        {"A": (ArrayDim(0, 1, 0, 2), ArrayDim(0, 2, 0, 3))}, ()
    )
    assert "((__i0) * 3 + __i1)" in checksum, checksum
    state_output = render_state_digest_function(
        {"A": (ArrayDim(0, 1, 0, 2), ArrayDim(0, 2, 0, 3))}, ("alpha",)
    )
    assert "polcert_observe_double(&ctx, &count, (double)alpha);" in state_output
    assert "polcert_observe_double(&ctx, &count, (double)A[__i0][__i1]);" in state_output
    print(
        "[generated-harness-unit] PASS expected=range-checks-and-Rocq-Z-integer-operators "
        "actual=parsed-state-observation-and-semantics-lowered "
        "interpretation=generated-C-harness-matches-control-arithmetic-and-hashes-every-modeled-value"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
