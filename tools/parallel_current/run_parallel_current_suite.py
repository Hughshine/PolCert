#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys
import tempfile
import textwrap


ROOT = pathlib.Path(__file__).resolve().parents[2]
POSITIVE_LOOP = textwrap.dedent(
    """\
    for i in range(0, 100) {
      for j in range(0, 4) {
        A[((4 * i) + j)] = ((2 * A[((4 * i) + j)]) + 2);
      }
    }
    """
)
DEPENDENT_LOOP = textwrap.dedent(
    """\
    for i in range(1, 100) {
      A[i] = (A[(i - 1)] + 1);
    }
    """
)


def run_polopt(polopt: pathlib.Path, loop_path: pathlib.Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(polopt), *args, str(loop_path)],
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        check=False,
    )


def require_success(name: str, proc: subprocess.CompletedProcess[str], needle: str) -> str | None:
    if proc.returncode != 0:
        return f"{name}: expected success, got exit {proc.returncode}"
    if needle not in proc.stdout:
        return f"{name}: missing {needle!r} in optimized loop"
    return None


def require_failure(name: str, proc: subprocess.CompletedProcess[str], needle: str) -> str | None:
    if proc.returncode == 0:
        return f"{name}: expected failure, but command succeeded"
    haystack = proc.stderr + proc.stdout
    if needle not in haystack:
        return f"{name}: missing {needle!r} in failure output"
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--polopt", default="./polopt")
    args = ap.parse_args()

    polopt = pathlib.Path(args.polopt).resolve()
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="parallel-current-") as tmp:
        tmpdir = pathlib.Path(tmp)
        positive = tmpdir / "positive.loop"
        dependent = tmpdir / "dependent.loop"
        positive.write_text(POSITIVE_LOOP)
        dependent.write_text(DEPENDENT_LOOP)

        checks = [
            (
                "parallel-current-positive",
                run_polopt(polopt, positive, "--parallel-current", "0"),
                require_success,
                "parallel for",
            ),
            (
                "parallel-current-positive-iss",
                run_polopt(polopt, positive, "--iss", "--parallel-current", "0"),
                require_success,
                "parallel for",
            ),
            (
                "parallel-current-out-of-bounds",
                run_polopt(polopt, positive, "--parallel-current", "5"),
                require_failure,
                "Parallel validation failed",
            ),
            (
                "parallel-current-dependent",
                run_polopt(polopt, dependent, "--parallel-current", "0"),
                require_failure,
                "Parallel validation failed",
            ),
        ]

        for name, proc, checker, needle in checks:
            failure = checker(name, proc, needle)
            if failure is not None:
                failures.append(
                    "{}\nstdout:\n{}\nstderr:\n{}".format(
                        failure,
                        proc.stdout,
                        proc.stderr,
                    )
                )

    if failures:
        print("[PARALLEL-CURRENT] FAIL")
        for failure in failures:
            print(failure)
        return 1

    print("[PARALLEL-CURRENT] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
