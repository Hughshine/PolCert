#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[2]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases-root", default="tests/polopt-generated/cases")
    ap.add_argument("--output-root", default="tests/end-to-end-generated/out")
    ap.add_argument("--benchmark-repeats", type=int, default=1)
    ap.add_argument("cases", nargs="*")
    args = ap.parse_args()

    cases_root = (ROOT / args.cases_root).resolve()
    runner = (ROOT / "tools/end_to_end_c/run_generated_case.py").resolve()
    if args.cases:
        case_dirs = [cases_root / name for name in args.cases]
    else:
        case_dirs = sorted(path for path in cases_root.iterdir() if path.is_dir())

    failed: list[str] = []
    for case_dir in case_dirs:
        proc = subprocess.run(
            [
                sys.executable,
                str(runner),
                str(case_dir),
                "--output-root",
                args.output_root,
                "--benchmark-repeats",
                str(args.benchmark_repeats),
            ],
            cwd=str(ROOT),
            text=True,
        )
        if proc.returncode != 0:
            failed.append(case_dir.name)

    if failed:
        print("[E2E-GEN-SUITE] FAIL")
        for name in failed:
            print(f"  - {name}")
        return 1

    print(f"[E2E-GEN-SUITE] OK cases={len(case_dirs)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
