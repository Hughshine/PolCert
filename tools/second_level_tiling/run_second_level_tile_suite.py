#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys
import tempfile
import textwrap


ROOT = pathlib.Path(__file__).resolve().parents[2]
MATMUL_INIT_LOOP = textwrap.dedent(
    """\
    context(N);

    for i in range(0, N) {
      for j in range(0, N) {
        C[i][j] = 0;
        for k in range(0, N) {
          C[i][j] = (C[i][j] + (A[i][k] * B[k][j]));
        }
      }
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
    with tempfile.TemporaryDirectory(prefix="second-level-tile-") as tmp:
        tmpdir = pathlib.Path(tmp)
        matmul_init = tmpdir / "matmul-init.loop"
        matmul_init.write_text(MATMUL_INIT_LOOP)

        checks = [
            (
                "second-level-tile-supported",
                run_polopt(polopt, matmul_init, "--second-level-tile"),
                require_success,
                "== Optimized Loop ==",
            ),
            (
                "second-level-tile-rejects-identity",
                run_polopt(polopt, matmul_init, "--second-level-tile", "--identity"),
                require_failure,
                "--second-level-tile requires a tiled Pluto phase and cannot be combined with --identity",
            ),
            (
                "second-level-tile-rejects-notile",
                run_polopt(polopt, matmul_init, "--second-level-tile", "--notile"),
                require_failure,
                "--second-level-tile requires tiling and cannot be combined with --notile",
            ),
            (
                "second-level-tile-rejects-parallel-current",
                run_polopt(polopt, matmul_init, "--second-level-tile", "--parallel-current", "0"),
                require_failure,
                "--second-level-tile is not yet supported with --parallel-current",
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
        print("[SECOND-LEVEL-TILE] FAIL")
        for failure in failures:
            print(failure)
        return 1

    print("[SECOND-LEVEL-TILE] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
