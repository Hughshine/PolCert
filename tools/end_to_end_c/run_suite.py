#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[2]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases-root", default="tests/end-to-end-c/cases")
    ap.add_argument("--output-root", default="tests/end-to-end-c/out")
    ap.add_argument("--polopt", default="./polopt")
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--benchmark-repeats", type=int, default=3)
    ap.add_argument("cases", nargs="*")
    args = ap.parse_args()

    cases_root = (ROOT / args.cases_root).resolve()
    run_case = (ROOT / "tools/end_to_end_c/run_case.py").resolve()
    if args.cases:
        case_dirs = [cases_root / name for name in args.cases]
    else:
        case_dirs = sorted(path for path in cases_root.iterdir() if path.is_dir())

    failed: list[str] = []
    for case_dir in case_dirs:
        proc = subprocess.run(
            [
                sys.executable,
                str(run_case),
                str(case_dir),
                "--polopt",
                args.polopt,
                "--output-root",
                args.output_root,
                "--timeout-seconds",
                str(args.timeout_seconds),
                "--benchmark-repeats",
                str(args.benchmark_repeats),
            ],
            cwd=str(ROOT),
            text=True,
        )
        if proc.returncode != 0:
            failed.append(case_dir.name)

    if failed:
        print("[E2E-SUITE] FAIL")
        for name in failed:
            print(f"  - {name}")
        return 1

    print("[E2E-SUITE] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
