#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import shutil
import subprocess
import time


ROOT = pathlib.Path(__file__).resolve().parents[2]
OPT_MARKER = "== Optimized Loop ==\n"


def has_parallel_loop(loop_text: str) -> bool:
    return "parallel for" in loop_text


def has_vector_loop(loop_text: str) -> bool:
    return "vector for" in loop_text


def loop_requires_openmp(loop_text: str) -> bool:
    return has_parallel_loop(loop_text) or has_vector_loop(loop_text)


def run(
    cmd: list[str],
    *,
    cwd: pathlib.Path | None = None,
    timeout: int | float | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd is not None else None,
        text=True,
        capture_output=True,
        timeout=timeout,
        env=env,
        check=False,
    )


def write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def recreate_dir(path: pathlib.Path) -> None:
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True, exist_ok=True)


def extract_optimized_loop(stdout: str) -> str:
    start = stdout.find(OPT_MARKER)
    if start < 0:
        return stdout
    start += len(OPT_MARKER)
    end = stdout.find("\n== ", start)
    if end < 0:
        end = len(stdout)
    return stdout[start:end].strip() + "\n"


def compile_c(src: pathlib.Path, exe: pathlib.Path, *, openmp: bool) -> subprocess.CompletedProcess[str]:
    cmd = ["cc", "-O3", "-std=c99", str(src), "-lm", "-o", str(exe)]
    if openmp:
        cmd.insert(1, "-fopenmp")
    return run(cmd)


def timed_run(
    exe: pathlib.Path,
    *,
    repeats: int,
    env: dict[str, str],
    timeout_seconds: int | float | None = None,
) -> tuple[str, float]:
    best = None
    stdout_ref = None
    for _ in range(repeats):
        started = time.perf_counter()
        proc = run([str(exe)], env=env, timeout=timeout_seconds)
        elapsed = time.perf_counter() - started
        if proc.returncode != 0:
            raise RuntimeError(
                f"program failed: {exe}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if stdout_ref is None:
            stdout_ref = proc.stdout
        elif proc.stdout != stdout_ref:
            raise RuntimeError(f"nondeterministic stdout for {exe}")
        best = elapsed if best is None else min(best, elapsed)
    assert stdout_ref is not None and best is not None
    return stdout_ref, best


def try_parse_float_lines(text: str) -> list[float] | None:
    vals: list[float] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        try:
            vals.append(float(stripped))
        except ValueError:
            return None
    return vals


def compare_numeric_outputs(
    baseline_stdout: str,
    optimized_stdout: str,
) -> dict[str, object]:
    baseline_vals = try_parse_float_lines(baseline_stdout)
    optimized_vals = try_parse_float_lines(optimized_stdout)
    if baseline_vals is None or optimized_vals is None:
        return {
            "numeric_comparable": False,
            "value_count_match": False,
            "max_abs_diff": None,
            "max_rel_diff": None,
        }
    if len(baseline_vals) != len(optimized_vals):
        return {
            "numeric_comparable": True,
            "value_count_match": False,
            "max_abs_diff": None,
            "max_rel_diff": None,
        }
    max_abs_diff = 0.0
    max_rel_diff = 0.0
    for baseline, optimized in zip(baseline_vals, optimized_vals):
        abs_diff = abs(baseline - optimized)
        scale = max(abs(baseline), abs(optimized), 1.0)
        rel_diff = abs_diff / scale
        max_abs_diff = max(max_abs_diff, abs_diff)
        max_rel_diff = max(max_rel_diff, rel_diff)
    return {
        "numeric_comparable": True,
        "value_count_match": True,
        "max_abs_diff": max_abs_diff,
        "max_rel_diff": max_rel_diff,
    }


def evaluate_outputs(
    baseline_stdout: str,
    optimized_stdout: str,
    *,
    abs_tolerance: float,
    rel_tolerance: float,
) -> dict[str, object]:
    exact_match = baseline_stdout == optimized_stdout
    numeric_summary = compare_numeric_outputs(baseline_stdout, optimized_stdout)
    numeric_within_tolerance = (
        bool(numeric_summary["numeric_comparable"])
        and bool(numeric_summary["value_count_match"])
        and float(numeric_summary["max_abs_diff"]) <= abs_tolerance
        and float(numeric_summary["max_rel_diff"]) <= rel_tolerance
    )
    return {
        "exact_match": exact_match,
        "numeric_comparable": numeric_summary["numeric_comparable"],
        "value_count_match": numeric_summary["value_count_match"],
        "max_abs_diff": numeric_summary["max_abs_diff"],
        "max_rel_diff": numeric_summary["max_rel_diff"],
        "numeric_within_tolerance": numeric_within_tolerance,
        "outputs_match": exact_match or numeric_within_tolerance,
    }


def fail_run(
    out_dir: pathlib.Path,
    *,
    which: str,
    reason: str,
    timeout_seconds: int | float | None = None,
    message: str | None = None,
) -> None:
    lines = [
        "result=fail",
        "stage=run",
        f"which={which}",
        f"reason={reason}",
    ]
    if timeout_seconds is not None:
        lines.append(f"timeout_seconds={timeout_seconds}")
    if message is not None:
        lines.append(f"message={message}")
    write_text(out_dir / "status.txt", "\n".join(lines) + "\n")
