#!/usr/bin/env python3
"""Exercise second-level diamond tiling across current and strict consumers."""

from __future__ import annotations

from itertools import product
from pathlib import Path
import subprocess


ROUTE = "[tiling-validation] route=general-fallback"
BASELINE_ROUTE = "[tiling-validation] route=permutable-band"


def route_lines(stderr: str) -> list[str]:
    return [
        line.strip()
        for line in stderr.splitlines()
        if line.strip().startswith("[tiling-validation] route=")
    ]


def optimized_loop(stdout: str) -> str:
    marker = "== Optimized Loop =="
    pos = stdout.find(marker)
    return stdout[pos:] if pos >= 0 else stdout


def check_second_level_diamond_route_matrix(
    *,
    polopt: Path,
    fixture: Path,
    timeout: int,
) -> None:
    tile_modes = ("--diamond-tile", "--full-diamond-tile")
    consumers = (
        ("parallel-current", ("--parallel-current", "0"), "parallel for"),
        ("vector-current", ("--vector-current", "0"), "vector for"),
        ("parallel-strict", ("--parallel", "--parallel-strict"), "parallel for"),
        ("vector-strict", ("--vector", "--vector-strict"), "vector for"),
        (
            "multipar-strict",
            (
                "--tile",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
                "--parallel",
                "--multipar",
                "--innerpar",
                "--parallel-strict",
            ),
            "parallel for",
        ),
    )
    for tile_mode, (consumer, consumer_args, loop_marker), use_iss in product(
        tile_modes, consumers, (False, True)
    ):
        label = f"second-level {tile_mode} {consumer}{' ISS' if use_iss else ''}"
        args = ["--second-level-tile", tile_mode, *consumer_args]
        if use_iss:
            args.append("--iss")
        try:
            proc = subprocess.run(
                [str(polopt), *args, str(fixture)],
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            raise AssertionError(f"{label} timed out after {timeout} seconds") from exc
        if proc.returncode != 0:
            raise AssertionError(
                f"{label} failed with exit {proc.returncode}\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if route_lines(proc.stderr) != [ROUTE]:
            raise AssertionError(
                f"{label} did not report exactly one explicit fallback route\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if "[alarm]" in proc.stderr or loop_marker not in proc.stdout or "32 *" not in proc.stdout:
            raise AssertionError(
                f"{label} omitted its accepted tiled {consumer} result\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        baseline_args = [tile_mode, *consumer_args]
        if use_iss:
            baseline_args.append("--iss")
        try:
            baseline = subprocess.run(
                [str(polopt), *baseline_args, str(fixture)],
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            raise AssertionError(f"{label} baseline timed out after {timeout} seconds") from exc
        if baseline.returncode != 0 or route_lines(baseline.stderr) != [BASELINE_ROUTE]:
            raise AssertionError(
                f"{label} baseline did not adopt exactly one permutable-band route\n"
                f"stdout:\n{baseline.stdout}\nstderr:\n{baseline.stderr}"
            )
        if "[alarm]" in baseline.stderr:
            raise AssertionError(f"{label} baseline reported an alarm")
        if optimized_loop(baseline.stdout) == optimized_loop(proc.stdout):
            raise AssertionError(
                f"{label} did not differ after removing --second-level-tile"
            )

    print("second-level diamond route matrix: PASS (20 current/strict variants)")


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    check_second_level_diamond_route_matrix(
        polopt=(root / "polopt").resolve(),
        fixture=(
            root
            / "tools"
            / "parallel_current"
            / "fixtures"
            / "diamond-example-inner-batch.loop"
        ),
        timeout=180,
    )
