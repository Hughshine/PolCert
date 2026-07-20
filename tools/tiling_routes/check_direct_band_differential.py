#!/usr/bin/env python3
"""Check the direct common-band validator against the two legacy scopes."""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[2]
RESULT_RE = re.compile(
    r"\[debug-band-tiling\] "
    r"old-strong=(true|false)\(ok=(true|false)\) "
    r"direct-band=(true|false)\(ok=(true|false)\) "
    r"whole=(true|false)\(ok=(true|false)\)"
)


def run_case(
    polopt: pathlib.Path,
    args: list[str],
    expected: tuple[bool, bool, bool],
    timeout: int,
) -> str | None:
    env = os.environ.copy()
    env["POLCERT_DEBUG_BAND_TILING"] = "1"
    env.setdefault("COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini"))
    with tempfile.TemporaryDirectory(prefix="polcert-direct-band-") as tmp:
        try:
            proc = subprocess.run(
                [str(polopt), *args],
                cwd=tmp,
                env=env,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return f"timed out after {timeout}s: {' '.join(args)}"

    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        return f"exit {proc.returncode}: {' '.join(args)}\n{output}"
    matches = RESULT_RE.findall(output)
    if len(matches) != 1:
        return f"expected one differential line, found {len(matches)}\n{output}"
    values = tuple(value == "true" for value in matches[0][0::2])
    alarms_ok = tuple(value == "true" for value in matches[0][1::2])
    if alarms_ok != (True, True, True):
        return f"checker alarm in {' '.join(args)}: {matches[0]}"
    if values != expected:
        return f"expected {expected}, got {values}: {' '.join(args)}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polopt", default="./polopt")
    parser.add_argument("--polcert", default="./polcert")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    polopt = pathlib.Path(args.polopt).resolve()
    polcert = pathlib.Path(args.polcert).resolve()
    if not polopt.is_file():
        raise SystemExit(f"missing polopt: {polopt}")
    if not polcert.is_file():
        raise SystemExit(f"missing polcert: {polcert}")

    cases = [
        (
            "ordinary-common-band",
            polopt,
            [str(ROOT / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop")],
            (True, True, True),
        ),
        (
            "mixed-depth-whole-program-only",
            polopt,
            [str(ROOT / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop")],
            (False, False, True),
        ),
        (
            "dependent-one-dimensional-band",
            polopt,
            [str(ROOT / "tools" / "parallel_current" / "fixtures" / "dependent.loop")],
            (True, True, True),
        ),
        (
            "frozen-diamond-phase-pair",
            polcert,
            [
                "--tiling",
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "diamond-tile-example.midtransform.scop"),
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "diamond-tile-example.posttile.scop"),
            ],
            (True, True, True),
        ),
    ]

    failures: list[str] = []
    for name, executable, command_args, expected in cases:
        failure = run_case(executable, command_args, expected, args.timeout)
        print(f"[direct-band-diff] {name}: {'PASS' if failure is None else 'FAIL'}")
        if failure is not None:
            failures.append(f"{name}: {failure}")
    if failures:
        print("[direct-band-diff] FAIL")
        print("\n".join(failures))
        return 1
    print(f"[direct-band-diff] OK ({len(cases)} cases, no alarms)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
