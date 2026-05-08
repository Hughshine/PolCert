#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


@dataclass
class CheckResult:
    name: str
    command: list[str]
    returncode: int
    elapsed_seconds: float
    stdout_path: str
    stderr_path: str

    @property
    def ok(self) -> bool:
        return self.returncode == 0


def run_check(name: str, command: list[str], out_dir: Path, timeout: int | None) -> CheckResult:
    out_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = out_dir / f"{name}.stdout.txt"
    stderr_path = out_dir / f"{name}.stderr.txt"
    start = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            cwd=str(ROOT),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        stdout = proc.stdout
        stderr = proc.stderr
        returncode = proc.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = (exc.stderr or "") + f"\n[artifact-check] timeout after {timeout} seconds\n"
        returncode = 124
    elapsed = time.monotonic() - start
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    return CheckResult(
        name=name,
        command=command,
        returncode=returncode,
        elapsed_seconds=elapsed,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
    )


def base_checks(
    out_dir: Path,
    diamond_timeout: int,
    identity_composition_limits: tuple[int, int] | None,
) -> list[tuple[str, list[str], int | None]]:
    identity_composition_command = [
        sys.executable,
        "tools/artifact/explore_identity_compositions.py",
        "--output-root",
        str(out_dir / "identity-compositions"),
    ]
    if identity_composition_limits is not None:
        diamond_limit, iss_limit = identity_composition_limits
        identity_composition_command.extend(
            [
                "--identity-diamond-limit",
                str(diamond_limit),
                "--identity-iss-limit",
                str(iss_limit),
            ]
        )
    return [
        (
            "py-compile-artifact-tools",
            [
                sys.executable,
                "-m",
                "py_compile",
                "tools/artifact/run_artifact_check.py",
                "tools/artifact/explore_codegen_gaps.py",
                "tools/artifact/explore_flag_effects.py",
                "tools/artifact/explore_identity_compositions.py",
                "tools/artifact/explore_unrolljam_effect_corpus.py",
                "tools/artifact/generate_capability_matrix.py",
                "tools/artifact/proof_report.py",
                "tools/end_to_end_c/loop_to_c.py",
                "tools/end_to_end_c/run_case.py",
                "tools/end_to_end_c/runner_common.py",
                "tools/diamond_tiling/run_pluto_diamond_suite.py",
                "tools/polopt_flag_suites/pluto_compat_driver.py",
                "tools/polopt_flag_suites/run_pluto_compat_suite.py",
            ],
            60,
        ),
        (
            "proof-report",
            [
                sys.executable,
                "tools/artifact/proof_report.py",
                "--json-out",
                str(out_dir / "proof-report.json"),
                "--markdown-out",
                str(out_dir / "proof-report.md"),
            ],
            60,
        ),
        (
            "capability-matrix",
            [
                sys.executable,
                "tools/artifact/generate_capability_matrix.py",
                "--json-out",
                str(out_dir / "capability-matrix.json"),
                "--markdown-out",
                str(out_dir / "capability-matrix.md"),
            ],
            60,
        ),
        (
            "codegen-gap-exploration",
            [
                sys.executable,
                "tools/artifact/explore_codegen_gaps.py",
                "--output-root",
                str(out_dir / "codegen-gaps"),
            ],
            60,
        ),
        (
            "unrolljam-effect-corpus",
            [
                sys.executable,
                "tools/artifact/explore_unrolljam_effect_corpus.py",
                "--output-root",
                str(out_dir / "unrolljam-effect-corpus"),
            ],
            180,
        ),
        (
            "identity-composition-exploration",
            identity_composition_command,
            180,
        ),
        (
            "pluto-compat-suite",
            [
                sys.executable,
                "tools/polopt_flag_suites/run_pluto_compat_suite.py",
                "--timeout",
                "30",
            ],
            900,
        ),
        (
            "end-to-end-c-const-unroll",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/const_unroll",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-unrolljam-block-variable",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/unrolljam_block_variable",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-unrolljam-dependent-guard",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/unrolljam_dependent_guard",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-stride-even",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/stride_even",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "end-to-end-c-stride-down",
            [
                sys.executable,
                "tools/end_to_end_c/run_case.py",
                "tests/end-to-end-c/cases/stride_down",
                "--polopt",
                "./polopt",
                "--output-root",
                str(out_dir / "end-to-end-c"),
                "--benchmark-repeats",
                "1",
            ],
            120,
        ),
        (
            "second-level-suite",
            [
                sys.executable,
                "tools/second_level_tiling/run_second_level_tile_suite.py",
                "--polopt",
                "./polopt",
            ],
            300,
        ),
        (
            "diamond-suite",
            [
                sys.executable,
                "tools/diamond_tiling/run_pluto_diamond_suite.py",
                "--timeout-seconds",
                str(diamond_timeout),
                "--output-root",
                str(out_dir / "diamond-suite"),
            ],
            max(600, diamond_timeout * 20),
        ),
    ]


def full_checks() -> list[tuple[str, list[str], int | None]]:
    return [
        ("check-admitted", ["make", "-s", "check-admitted"], 120),
        ("strict-loop-suite", ["make", "test-polopt-loop-suite"], None),
        ("iss-suite", ["make", "test-iss-pluto-suite"], None),
        ("parallel-current-suite", ["make", "test-parallel-current-suite"], None),
    ]


def extended_checks(out_dir: Path) -> list[tuple[str, list[str], int | None]]:
    return [
        (
            "flag-effect-exploration",
            [
                sys.executable,
                "tools/artifact/explore_flag_effects.py",
                "--json-out",
                str(out_dir / "flag-effects.json"),
                "--markdown-out",
                str(out_dir / "flag-effects.md"),
                "--limit-per-pair",
                "2",
                "--timeout",
                "20",
            ],
            1800,
        )
    ]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["smoke", "full", "extended"], default="smoke")
    ap.add_argument("--output-root", default="/tmp/polcert-artifact-check")
    ap.add_argument("--diamond-timeout-seconds", type=int, default=180)
    args = ap.parse_args()

    out_dir = Path(args.output_root).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    # Smoke mode is for artifact health checks, not for exhaustive route search.
    # Full/extended modes keep the unbounded identity-composition exploration.
    identity_composition_limits = (16, 16) if args.mode == "smoke" else None
    checks = base_checks(out_dir, args.diamond_timeout_seconds, identity_composition_limits)
    if args.mode in ("full", "extended"):
        checks.extend(full_checks())
    if args.mode == "extended":
        checks.extend(extended_checks(out_dir))

    results: list[CheckResult] = []
    for name, command, timeout in checks:
        print(f"[artifact-check] {name}: running")
        result = run_check(name, command, out_dir, timeout)
        results.append(result)
        status = "PASS" if result.ok else f"FAIL exit={result.returncode}"
        print(f"[artifact-check] {name}: {status} ({result.elapsed_seconds:.1f}s)")
        if not result.ok:
            break

    summary = {
        "root": str(ROOT),
        "mode": args.mode,
        "output_root": str(out_dir),
        "environment": {
            "POLCERT_PLUTO": os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"),
            "PLUTO_TEST_DIR": os.environ.get("PLUTO_TEST_DIR", "/pluto/test"),
        },
        "results": [dict(asdict(item), ok=item.ok) for item in results],
        "ok": all(item.ok for item in results),
    }
    (out_dir / "artifact-results.json").write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(f"[artifact-check] summary: {out_dir / 'artifact-results.json'}")
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
