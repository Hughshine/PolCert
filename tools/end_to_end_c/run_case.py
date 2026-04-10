#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys
import time

from loop_to_c import transpile_loop_text


ROOT = pathlib.Path(__file__).resolve().parents[2]
KERNEL_MARKER = "/* POLCERT_KERNEL */"
OPT_MARKER = "== Optimized Loop ==\n"


def run(cmd: list[str], *, cwd: pathlib.Path | None = None, timeout: int | None = None, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
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
    timeout_seconds: int | None = None,
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


def render_source(template: str, kernel_c: str) -> str:
    if KERNEL_MARKER not in template:
        raise ValueError(f"missing kernel marker {KERNEL_MARKER!r}")
    return template.replace(KERNEL_MARKER, kernel_c.rstrip())


def load_meta(case_dir: pathlib.Path) -> dict[str, object]:
    return json.loads((case_dir / "meta.json").read_text())


def bool_from_meta(meta: dict[str, object], key: str, default: bool = False) -> bool:
    value = meta.get(key, default)
    if not isinstance(value, bool):
        raise ValueError(f"{key} must be a bool")
    return value


def list_from_meta(meta: dict[str, object], key: str) -> list[str]:
    value = meta.get(key, [])
    if not isinstance(value, list) or not all(isinstance(x, str) for x in value):
        raise ValueError(f"{key} must be a string list")
    return list(value)


def float_from_meta(meta: dict[str, object], key: str, default: float = 0.0) -> float:
    value = meta.get(key, default)
    if not isinstance(value, (int, float)):
        raise ValueError(f"{key} must be numeric")
    return float(value)


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
    for b, o in zip(baseline_vals, optimized_vals):
        abs_diff = abs(b - o)
        scale = max(abs(b), abs(o), 1.0)
        rel_diff = abs_diff / scale
        max_abs_diff = max(max_abs_diff, abs_diff)
        max_rel_diff = max(max_rel_diff, rel_diff)
    return {
        "numeric_comparable": True,
        "value_count_match": True,
        "max_abs_diff": max_abs_diff,
        "max_rel_diff": max_rel_diff,
    }


def fail_run(
    out_dir: pathlib.Path,
    *,
    which: str,
    reason: str,
    timeout_seconds: int | None = None,
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("case_dir")
    ap.add_argument("--polopt", default="./polopt")
    ap.add_argument("--polopt-arg", action="append", default=[])
    ap.add_argument("--output-root", default="tests/end-to-end-c/out")
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--benchmark-repeats", type=int, default=3)
    ap.add_argument("--require-parallelized", action="store_true")
    ap.add_argument("--keep-going", action="store_true")
    args = ap.parse_args()

    case_dir = pathlib.Path(args.case_dir).resolve()
    meta = load_meta(case_dir)
    case_name = case_dir.name
    out_dir = (ROOT / args.output_root / case_name).resolve()
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    loop_path = (case_dir / meta["loop"]).resolve()
    template_path = (case_dir / "wrapper.c.in").resolve()
    polopt = pathlib.Path(args.polopt).resolve()
    polopt_args = list_from_meta(meta, "polopt_args")
    benchmark = bool_from_meta(meta, "benchmark", default=True)
    openmp = bool_from_meta(meta, "openmp", default=False)
    abs_tolerance = float_from_meta(meta, "abs_tolerance", default=0.0)
    rel_tolerance = float_from_meta(meta, "rel_tolerance", default=0.0)

    template = template_path.read_text()
    input_loop = loop_path.read_text()

    write_text(out_dir / "input.loop", input_loop)
    baseline_kernel = transpile_loop_text(input_loop)
    baseline_src = render_source(template, baseline_kernel)
    write_text(out_dir / "baseline.kernel.c", baseline_kernel)
    write_text(out_dir / "baseline.c", baseline_src)

    polopt_cmd = [str(polopt), *polopt_args, *args.polopt_arg, str(loop_path)]
    try:
        proc = run(polopt_cmd, cwd=ROOT, timeout=args.timeout_seconds)
    except subprocess.TimeoutExpired:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=polopt\nreason=timeout\n"
            f"timeout_seconds={args.timeout_seconds}\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] polopt timed out")
    write_text(out_dir / "polopt.stdout.txt", proc.stdout)
    write_text(out_dir / "polopt.stderr.txt", proc.stderr)
    if proc.returncode != 0:
        write_text(
            out_dir / "status.txt",
            f"result=fail\nstage=polopt\nexit_code={proc.returncode}\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] polopt failed")

    optimized_loop = extract_optimized_loop(proc.stdout)
    parallelized_loop = "parallel for" in optimized_loop
    write_text(out_dir / "optimized.loop", optimized_loop)
    if args.require_parallelized and not parallelized_loop:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=parallelize\nparallelized_loop=false\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] no parallel for emitted")
    optimized_kernel = transpile_loop_text(optimized_loop)
    optimized_src = render_source(template, optimized_kernel)
    write_text(out_dir / "optimized.kernel.c", optimized_kernel)
    write_text(out_dir / "optimized.c", optimized_src)

    baseline_exe = out_dir / "baseline.exe"
    optimized_exe = out_dir / "optimized.exe"
    compile_with_openmp = openmp or parallelized_loop
    baseline_build = compile_c(out_dir / "baseline.c", baseline_exe, openmp=compile_with_openmp)
    optimized_build = compile_c(out_dir / "optimized.c", optimized_exe, openmp=compile_with_openmp)
    write_text(out_dir / "baseline.build.stderr.txt", baseline_build.stderr)
    write_text(out_dir / "optimized.build.stderr.txt", optimized_build.stderr)
    if baseline_build.returncode != 0 or optimized_build.returncode != 0:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=compile\n"
            f"baseline_exit={baseline_build.returncode}\n"
            f"optimized_exit={optimized_build.returncode}\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] compile failed")

    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", "1")

    try:
        baseline_stdout, baseline_best = timed_run(
            baseline_exe,
            repeats=args.benchmark_repeats if benchmark else 1,
            env=env,
            timeout_seconds=args.timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        fail_run(
            out_dir,
            which="baseline",
            reason="timeout",
            timeout_seconds=args.timeout_seconds,
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] baseline executable timed out")
    except RuntimeError as err:
        fail_run(
            out_dir,
            which="baseline",
            reason="runtime_error",
            message=str(err),
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] baseline executable failed")
    try:
        optimized_stdout, optimized_best = timed_run(
            optimized_exe,
            repeats=args.benchmark_repeats if benchmark else 1,
            env=env,
            timeout_seconds=args.timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        fail_run(
            out_dir,
            which="optimized",
            reason="timeout",
            timeout_seconds=args.timeout_seconds,
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] optimized executable timed out")
    except RuntimeError as err:
        fail_run(
            out_dir,
            which="optimized",
            reason="runtime_error",
            message=str(err),
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] optimized executable failed")
    write_text(out_dir / "baseline.stdout.txt", baseline_stdout)
    write_text(out_dir / "optimized.stdout.txt", optimized_stdout)
    exact_match = baseline_stdout == optimized_stdout
    numeric_summary = compare_numeric_outputs(baseline_stdout, optimized_stdout)
    numeric_within_tolerance = (
        bool(numeric_summary["numeric_comparable"])
        and bool(numeric_summary["value_count_match"])
        and float(numeric_summary["max_abs_diff"]) <= abs_tolerance
        and float(numeric_summary["max_rel_diff"]) <= rel_tolerance
    )
    outputs_match = exact_match or numeric_within_tolerance
    speedup = (baseline_best / optimized_best) if optimized_best > 0 else 0.0
    summary = {
        "result": "ok" if outputs_match else "fail",
        "outputs_match": outputs_match,
        "exact_match": exact_match,
        "parallelized_loop": parallelized_loop,
        "numeric_comparable": numeric_summary["numeric_comparable"],
        "value_count_match": numeric_summary["value_count_match"],
        "max_abs_diff": numeric_summary["max_abs_diff"],
        "max_rel_diff": numeric_summary["max_rel_diff"],
        "abs_tolerance": abs_tolerance,
        "rel_tolerance": rel_tolerance,
        "numeric_within_tolerance": numeric_within_tolerance,
        "baseline_best_seconds": baseline_best,
        "optimized_best_seconds": optimized_best,
        "speedup": speedup,
        "polopt_args": [*polopt_args, *args.polopt_arg],
    }
    write_text(out_dir / "summary.json", json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_text(
        out_dir / "status.txt",
        "result={}\noutputs_match={}\nexact_match={}\nparallelized_loop={}\nnumeric_comparable={}\nvalue_count_match={}\nmax_abs_diff={}\nmax_rel_diff={}\nabs_tolerance={:.3e}\nrel_tolerance={:.3e}\nnumeric_within_tolerance={}\nbaseline_best_seconds={:.6f}\noptimized_best_seconds={:.6f}\nspeedup={:.4f}\n".format(
            "ok" if outputs_match else "fail",
            str(outputs_match).lower(),
            str(exact_match).lower(),
            str(parallelized_loop).lower(),
            str(bool(numeric_summary["numeric_comparable"])).lower(),
            str(bool(numeric_summary["value_count_match"])).lower(),
            numeric_summary["max_abs_diff"],
            numeric_summary["max_rel_diff"],
            abs_tolerance,
            rel_tolerance,
            str(numeric_within_tolerance).lower(),
            baseline_best,
            optimized_best,
            speedup,
        ),
    )
    if not outputs_match:
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] output mismatch")

    print(
        f"[E2E] {case_name}: ok "
        f"baseline={baseline_best:.4f}s optimized={optimized_best:.4f}s speedup={speedup:.3f}x "
        f"parallelized_loop={str(parallelized_loop).lower()} "
        f"exact_match={str(exact_match).lower()} "
        f"max_abs_diff={numeric_summary['max_abs_diff']} "
        f"max_rel_diff={numeric_summary['max_rel_diff']}"
    )
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
