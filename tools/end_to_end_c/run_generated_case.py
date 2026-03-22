#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import sys

from generated_harness import build_harness, render_program_source
from run_case import compare_numeric_outputs, compile_c, timed_run, write_text


ROOT = pathlib.Path(__file__).resolve().parents[2]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("case_dir")
    ap.add_argument("--output-root", default="tests/end-to-end-generated/out")
    ap.add_argument("--benchmark-repeats", type=int, default=1)
    args = ap.parse_args()

    case_dir = pathlib.Path(args.case_dir).resolve()
    case_name = case_dir.name
    out_dir = (ROOT / args.output_root / case_name).resolve()
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    input_loop = (case_dir / "input.loop").read_text()
    optimized_loop = (case_dir / "optimized.loop").read_text()
    info = build_harness(case_name, input_loop, optimized_loop)

    write_text(out_dir / "input.loop", input_loop)
    write_text(out_dir / "optimized.loop", optimized_loop)
    write_text(out_dir / "baseline.kernel.c", info.baseline_kernel)
    write_text(out_dir / "optimized.kernel.c", info.optimized_kernel)
    write_text(out_dir / "baseline.c", render_program_source(info, optimized=False))
    write_text(out_dir / "optimized.c", render_program_source(info, optimized=True))

    baseline_exe = out_dir / "baseline.exe"
    optimized_exe = out_dir / "optimized.exe"
    baseline_build = compile_c(out_dir / "baseline.c", baseline_exe, openmp=info.openmp)
    optimized_build = compile_c(out_dir / "optimized.c", optimized_exe, openmp=info.openmp)
    write_text(out_dir / "baseline.build.stderr.txt", baseline_build.stderr)
    write_text(out_dir / "optimized.build.stderr.txt", optimized_build.stderr)
    if baseline_build.returncode != 0 or optimized_build.returncode != 0:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=compile\n"
            f"baseline_exit={baseline_build.returncode}\n"
            f"optimized_exit={optimized_build.returncode}\n",
        )
        print(f"[E2E-GEN] {case_name}: compile failed")
        return 1

    env = dict(**__import__("os").environ)
    env.setdefault("OMP_NUM_THREADS", "1")
    baseline_stdout, baseline_best = timed_run(baseline_exe, repeats=args.benchmark_repeats, env=env)
    optimized_stdout, optimized_best = timed_run(optimized_exe, repeats=args.benchmark_repeats, env=env)
    write_text(out_dir / "baseline.stdout.txt", baseline_stdout)
    write_text(out_dir / "optimized.stdout.txt", optimized_stdout)

    exact_match = baseline_stdout == optimized_stdout
    numeric_summary = compare_numeric_outputs(baseline_stdout, optimized_stdout)
    outputs_match = exact_match or (
        bool(numeric_summary["numeric_comparable"])
        and bool(numeric_summary["value_count_match"])
        and float(numeric_summary["max_abs_diff"]) == 0.0
        and float(numeric_summary["max_rel_diff"]) == 0.0
    )
    speedup = (baseline_best / optimized_best) if optimized_best > 0 else 0.0
    summary = {
        "result": "ok" if outputs_match else "fail",
        "outputs_match": outputs_match,
        "exact_match": exact_match,
        "numeric_comparable": numeric_summary["numeric_comparable"],
        "value_count_match": numeric_summary["value_count_match"],
        "max_abs_diff": numeric_summary["max_abs_diff"],
        "max_rel_diff": numeric_summary["max_rel_diff"],
        "baseline_best_seconds": baseline_best,
        "optimized_best_seconds": optimized_best,
        "speedup": speedup,
        "params": info.params,
        "openmp": info.openmp,
    }
    write_text(out_dir / "summary.json", json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_text(
        out_dir / "status.txt",
        "result={}\noutputs_match={}\nexact_match={}\nnumeric_comparable={}\nvalue_count_match={}\nmax_abs_diff={}\nmax_rel_diff={}\nbaseline_best_seconds={:.6f}\noptimized_best_seconds={:.6f}\nspeedup={:.4f}\n".format(
            "ok" if outputs_match else "fail",
            str(outputs_match).lower(),
            str(exact_match).lower(),
            str(bool(numeric_summary["numeric_comparable"])).lower(),
            str(bool(numeric_summary["value_count_match"])).lower(),
            numeric_summary["max_abs_diff"],
            numeric_summary["max_rel_diff"],
            baseline_best,
            optimized_best,
            speedup,
        ),
    )
    if not outputs_match:
        print(
            f"[E2E-GEN] {case_name}: output mismatch "
            f"max_abs_diff={numeric_summary['max_abs_diff']} "
            f"max_rel_diff={numeric_summary['max_rel_diff']}"
        )
        return 1

    print(
        f"[E2E-GEN] {case_name}: ok "
        f"baseline={baseline_best:.4f}s optimized={optimized_best:.4f}s "
        f"speedup={speedup:.3f}x exact_match={str(exact_match).lower()} "
        f"max_abs_diff={numeric_summary['max_abs_diff']} "
        f"max_rel_diff={numeric_summary['max_rel_diff']}"
    )
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
