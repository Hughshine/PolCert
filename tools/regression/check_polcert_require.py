#!/usr/bin/env python3
"""Check the exit status selected by polcert's two-input --require option."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests" / "polcert-require"
BEFORE = FIXTURES / "dfp-skew.before.scop"
AFTER = FIXTURES / "dfp-skew.after.scop"
TILING = ROOT / "tools" / "tiling_routes" / "fixtures"
TILING_MID = TILING / "diamond-tile-example.midtransform.scop"
TILING_POST = TILING / "diamond-tile-example.posttile.scop"


def require(value: str | None) -> list[str]:
    return [] if value is None else ["--require", value]


def cases() -> list[tuple[str, list[str], int, str | None]]:
    """Return (name, arguments, expected exit status, expected tag)."""
    before, after = str(BEFORE), str(AFTER)
    mid, post = str(TILING_MID), str(TILING_POST)
    rows: list[tuple[str, list[str], int, str | None]] = []
    # Only "before refines after" holds: the faulty DFP schedule ties a
    # conflicting pair, so after admits an order that before excludes.
    for value, status in ((None, 1), ("equiv", 1), ("refines", 1), ("refined-by", 0)):
        rows.append((f"lt-{value or 'default'}", [*require(value), before, after], status, "[LT]"))
    rows.append(("lt-affine-default", ["--affine", before, after], 1, "[LT]"))
    # Swapping the files gives the converse relation.
    for value, status in ((None, 0), ("equiv", 1), ("refines", 0), ("refined-by", 1)):
        rows.append((f"gt-{value or 'default'}", [*require(value), after, before], status, "[GT]"))
    for value in (None, "equiv", "refines", "refined-by"):
        rows.append((f"eq-{value or 'default'}", [*require(value), before, before], 0, "[EQ]"))
    rows.append(("tiling-refines", ["--tiling", *require("refines"), mid, post], 0, "[TILING-OK]"))
    rows.append(("tiling-equiv-usage", ["--tiling", *require("equiv"), mid, post], 2, None))
    rows.append(("tiling-refined-by-usage", ["--tiling", *require("refined-by"), mid, post], 2, None))
    rows.append(("phase-refined-by-usage", [*require("refined-by"), before, before, after], 2, None))
    rows.append(("auto-tiling-fallback", [mid, post], 0, "[TILING-OK]"))
    rows.append(("unknown-value", [*require("both"), before, after], 2, None))
    return rows


def run_case(polcert: Path, args: list[str], timeout: int) -> tuple[int, str]:
    proc = subprocess.run(
        [str(polcert), *args],
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )
    return proc.returncode, proc.stdout + proc.stderr


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polcert", default="./polcert")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    polcert = Path(args.polcert).resolve()
    if not polcert.is_file():
        raise SystemExit(f"missing polcert: {polcert}")

    failures: list[str] = []
    rows = cases()
    for name, arguments, expected_status, expected_tag in rows:
        try:
            status, output = run_case(polcert, arguments, args.timeout)
        except subprocess.TimeoutExpired:
            status, output = -1, f"timed out after {args.timeout}s"
        problem = None
        if status != expected_status:
            problem = f"exit {status}, expected {expected_status}"
        elif expected_tag is not None and expected_tag not in output:
            problem = f"missing {expected_tag}"
        elif expected_status == 1 and "[REQUIRE-FAIL]" not in output:
            problem = "missing [REQUIRE-FAIL]"
        print(f"[polcert-require] {name}: {'PASS' if problem is None else 'FAIL'}")
        if problem is not None:
            failures.append(f"{name}: {problem}\n{output}")

    if failures:
        print("[polcert-require] FAIL")
        print("\n".join(failures))
        return 1
    print(f"[polcert-require] OK ({len(rows)} cases)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
