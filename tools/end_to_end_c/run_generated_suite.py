#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys

from generated_harness import DEFAULT_TIER


ROOT = pathlib.Path(__file__).resolve().parents[2]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases-root", default="tests/polopt-generated/cases")
    ap.add_argument("--polopt")
    ap.add_argument("--polopt-arg", action="append", default=[])
    ap.add_argument("--output-root", default="tests/end-to-end-generated/out")
    ap.add_argument("--benchmark-repeats", type=int, default=1)
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--omp-threads", type=int, default=1)
    ap.add_argument("--require-parallelized", action="store_true")
    ap.add_argument("--tier", default=DEFAULT_TIER)
    ap.add_argument(
        "--param-config",
        default="tests/end-to-end-generated/param_tiers.json",
    )
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
        cmd = [
            sys.executable,
            str(runner),
            str(case_dir),
            "--output-root",
            args.output_root,
            "--benchmark-repeats",
            str(args.benchmark_repeats),
            "--timeout-seconds",
            str(args.timeout_seconds),
            "--omp-threads",
            str(args.omp_threads),
            "--tier",
            args.tier,
            "--param-config",
            args.param_config,
        ]
        if args.polopt:
            cmd.extend(["--polopt", args.polopt])
            for arg in args.polopt_arg:
                cmd.append(f"--polopt-arg={arg}")
            if args.require_parallelized:
                cmd.append("--require-parallelized")
        proc = subprocess.run(
            cmd,
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
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
