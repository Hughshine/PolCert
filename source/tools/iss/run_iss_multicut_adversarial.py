#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "tests" / "iss-pluto-dumps"
POLOPT = ROOT / "polopt"


def run_bridge(path: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [str(POLOPT), "--validate-iss-bridge", str(path)],
        capture_output=True,
        text=True,
        check=False,
    )
    output = (proc.stdout + "\n" + proc.stderr).strip()
    return proc.returncode, output


def main() -> int:
    cases = [
        (
            "multicut-complete",
            DATA / "multicut_valid.bridge",
            0,
            "validation: OK (coq complete-cut-shape)",
            "all-four-sign-regions-proved",
        ),
        (
            "pluto-three-cut-four-piece-mismatch",
            DATA / "multicut_native_mismatch.bridge",
            1,
            "validation: FAIL",
            "incomplete-three-cut-sign-space-rejected",
        ),
        (
            "two-cut-missing-piece",
            DATA / "multicut_missing_piece.bridge",
            1,
            "validation: FAIL",
            "missing-sign-region-rejected",
        ),
    ]
    failures: list[str] = []

    for label, fixture, expected_code, marker, interpretation in cases:
        code, output = run_bridge(fixture)
        matched = code == expected_code and marker in output
        expected = "accept" if expected_code == 0 else "reject"
        actual = "accept" if code == 0 else "reject"
        print(
            f"[ISS-MULTICUT] {'PASS' if matched else 'FAIL'} case={label} "
            f"expected={expected},exit:{expected_code} actual={actual},exit:{code} "
            f"interpretation={interpretation}"
        )
        if not matched:
            failures.append(
                f"{label}: expected exit {expected_code} and {marker!r}; "
                f"got exit {code}\n{output}"
            )

    if failures:
        print("[ISS-MULTICUT] FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        "[ISS-MULTICUT] PASS expected=accepted:1,rejected:2 "
        "actual=accepted:1,rejected:2 interpretation=complete-cut-boundary-matched"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
