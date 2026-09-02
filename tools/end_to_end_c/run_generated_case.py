#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import sys

from generated_harness import DEFAULT_TIER, build_harness, load_param_tiers, render_program_source
from runner_common import (
    ROOT,
    compile_c,
    evaluate_outputs,
    extract_optimized_loop,
    fail_run,
    has_parallel_loop,
    has_vector_loop,
    recreate_dir,
    run,
    timed_run,
    write_text,
)

DEFAULT_ABS_TOLERANCE = 1e-9
DEFAULT_REL_TOLERANCE = 1e-9


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return parsed


def normalized_loop_text(text: str) -> str:
    return "\n".join(line.rstrip() for line in text.strip().splitlines())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("case_dir")
    ap.add_argument("--polopt")
    ap.add_argument("--polopt-arg", action="append", default=[])
    ap.add_argument("--pipeline-name", default="")
    ap.add_argument("--harness-case-name")
    ap.add_argument("--use-input-loop-as-optimized", action="store_true")
    ap.add_argument("--output-root", default="tests/end-to-end-generated/out")
    ap.add_argument("--benchmark-repeats", type=positive_int, default=1)
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--omp-threads", type=positive_int, default=1)
    ap.add_argument("--require-parallelized", action="store_true")
    ap.add_argument("--require-vectorized", action="store_true")
    ap.add_argument("--optimized-loop-needle", action="append", default=[])
    ap.add_argument(
        "--require-optimized-loop-differs-from-cached", action="store_true"
    )
    ap.add_argument("--abs-tolerance", type=float, default=DEFAULT_ABS_TOLERANCE)
    ap.add_argument("--rel-tolerance", type=float, default=DEFAULT_REL_TOLERANCE)
    ap.add_argument("--tier", default=DEFAULT_TIER)
    ap.add_argument(
        "--param-config",
        default="tests/end-to-end-generated/param_tiers.json",
    )
    args = ap.parse_args()

    case_dir = pathlib.Path(args.case_dir).resolve()
    case_name = case_dir.name
    harness_case_name = args.harness_case_name or case_name
    out_dir = (ROOT / args.output_root / case_name).resolve()
    recreate_dir(out_dir)

    input_loop = (case_dir / "input.loop").read_text()
    if args.use_input_loop_as_optimized:
        optimized_loop = input_loop
    elif args.polopt:
        polopt = pathlib.Path(args.polopt).resolve()
        polopt_env = os.environ.copy()
        polopt_env.setdefault(
            "COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini")
        )
        try:
            proc = run(
                [str(polopt), *args.polopt_arg, str(case_dir / "input.loop")],
                cwd=ROOT,
                timeout=args.timeout_seconds,
                env=polopt_env,
            )
        except subprocess.TimeoutExpired:
            write_text(
                out_dir / "status.txt",
                "result=fail\nstage=polopt\nreason=timeout\n"
                f"timeout_seconds={args.timeout_seconds}\n",
            )
            print(f"[E2E-GEN] {case_name}: polopt timed out")
            return 1
        write_text(out_dir / "polopt.stdout.txt", proc.stdout)
        write_text(out_dir / "polopt.stderr.txt", proc.stderr)
        if proc.returncode != 0:
            write_text(
                out_dir / "status.txt",
                "result=fail\nstage=polopt\n"
                f"exit_code={proc.returncode}\n",
            )
            print(f"[E2E-GEN] {case_name}: polopt failed")
            return 1
        optimized_loop = extract_optimized_loop(proc.stdout)
    else:
        optimized_loop = (case_dir / "optimized.loop").read_text()
    for needle in args.optimized_loop_needle:
        if needle not in optimized_loop:
            write_text(
                out_dir / "status.txt",
                "result=fail\nstage=optimized-loop-effect\n"
                f"reason=missing marker: {needle}\n",
            )
            print(
                f"[E2E-GEN] FAIL case={case_name} expected=marker:{needle!r} "
                "actual=missing interpretation=requested-optimization-effect-was-not-observed"
            )
            return 1
    if args.require_optimized_loop_differs_from_cached:
        cached_loop = (case_dir / "optimized.loop").read_text()
        if normalized_loop_text(optimized_loop) == normalized_loop_text(cached_loop):
            write_text(
                out_dir / "status.txt",
                "result=fail\nstage=optimized-loop-effect\n"
                "reason=live output equals cached default output\n",
            )
            print(
                f"[E2E-GEN] FAIL case={case_name} expected=differs-from-cached-default "
                "actual=equal interpretation=requested-route-had-no-observable-effect"
            )
            return 1
    tier_overrides = load_param_tiers((ROOT / args.param_config).resolve())
    info = build_harness(
        harness_case_name,
        input_loop,
        optimized_loop,
        tier=args.tier,
        tier_overrides=tier_overrides,
    )

    write_text(out_dir / "input.loop", input_loop)
    write_text(out_dir / "optimized.loop", optimized_loop)
    write_text(out_dir / "baseline.kernel.c", info.baseline_kernel)
    write_text(out_dir / "optimized.kernel.c", info.optimized_kernel)
    parallelized_loop = has_parallel_loop(optimized_loop)
    vectorized_loop = has_vector_loop(optimized_loop)
    if args.require_parallelized and not parallelized_loop:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=parallelize\nparallelized_loop=false\n",
        )
        print(f"[E2E-GEN] {case_name}: no parallel for emitted")
        return 1
    if args.require_vectorized and not vectorized_loop:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=vectorize\nvectorized_loop=false\n",
        )
        print(f"[E2E-GEN] {case_name}: no vector for emitted")
        return 1
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

    env = os.environ.copy()
    env["OMP_NUM_THREADS"] = str(args.omp_threads)
    env["OMP_DYNAMIC"] = "FALSE"
    try:
        baseline_stdout, baseline_best = timed_run(
            baseline_exe,
            repeats=args.benchmark_repeats,
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
        print(f"[E2E-GEN] {case_name}: baseline executable timed out")
        return 1
    except RuntimeError as err:
        fail_run(
            out_dir,
            which="baseline",
            reason="runtime_error",
            message=str(err),
        )
        print(f"[E2E-GEN] {case_name}: baseline executable failed")
        return 1
    try:
        optimized_stdout, optimized_best = timed_run(
            optimized_exe,
            repeats=args.benchmark_repeats,
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
        print(f"[E2E-GEN] {case_name}: optimized executable timed out")
        return 1
    except RuntimeError as err:
        fail_run(
            out_dir,
            which="optimized",
            reason="runtime_error",
            message=str(err),
        )
        print(f"[E2E-GEN] {case_name}: optimized executable failed")
        return 1
    write_text(out_dir / "baseline.stdout.txt", baseline_stdout)
    write_text(out_dir / "optimized.stdout.txt", optimized_stdout)

    comparison = evaluate_outputs(
        baseline_stdout,
        optimized_stdout,
        abs_tolerance=args.abs_tolerance,
        rel_tolerance=args.rel_tolerance,
    )
    exact_match = bool(comparison["exact_match"])
    numeric_within_tolerance = bool(comparison["numeric_within_tolerance"])
    outputs_match = bool(comparison["outputs_match"])
    speedup = (baseline_best / optimized_best) if optimized_best > 0 else 0.0
    summary = {
        "case": case_name,
        "pipeline_name": args.pipeline_name,
        "result": "ok" if outputs_match else "fail",
        "outputs_match": outputs_match,
        "exact_match": exact_match,
        "numeric_comparable": comparison["numeric_comparable"],
        "numeric_finite": comparison["numeric_finite"],
        "value_count_match": comparison["value_count_match"],
        "max_abs_diff": comparison["max_abs_diff"],
        "max_rel_diff": comparison["max_rel_diff"],
        "abs_tolerance": args.abs_tolerance,
        "rel_tolerance": args.rel_tolerance,
        "numeric_within_tolerance": numeric_within_tolerance,
        "baseline_best_seconds": baseline_best,
        "optimized_best_seconds": optimized_best,
        "speedup": speedup,
        "params": info.params,
        "openmp": info.openmp,
        "omp_threads_requested": args.omp_threads,
        "execution_repeats": args.benchmark_repeats,
        "parallelized_loop": parallelized_loop,
        "vectorized_loop": vectorized_loop,
        "optimized_loop_source": (
            "input"
            if args.use_input_loop_as_optimized
            else ("polopt" if args.polopt else "cached_default_no_iss_affine_tiling")
        ),
        "polopt_args": args.polopt_arg,
        "tier": args.tier,
    }
    write_text(out_dir / "summary.json", json.dumps(summary, indent=2, sort_keys=True) + "\n")
    write_text(
        out_dir / "status.txt",
        "result={}\npipeline_name={}\noptimized_loop_source={}\noutputs_match={}\nexact_match={}\nnumeric_comparable={}\nnumeric_finite={}\nvalue_count_match={}\nparallelized_loop={}\nvectorized_loop={}\nomp_threads_requested={}\nexecution_repeats={}\nmax_abs_diff={}\nmax_rel_diff={}\nabs_tolerance={:.3e}\nrel_tolerance={:.3e}\nnumeric_within_tolerance={}\nbaseline_best_seconds={:.6f}\noptimized_best_seconds={:.6f}\nspeedup={:.4f}\n".format(
            "ok" if outputs_match else "fail",
            args.pipeline_name,
            (
                "input"
                if args.use_input_loop_as_optimized
                else ("polopt" if args.polopt else "cached_default_no_iss_affine_tiling")
            ),
            str(outputs_match).lower(),
            str(exact_match).lower(),
            str(bool(comparison["numeric_comparable"])).lower(),
            str(bool(comparison["numeric_finite"])).lower(),
            str(bool(comparison["value_count_match"])).lower(),
            str(parallelized_loop).lower(),
            str(vectorized_loop).lower(),
            args.omp_threads,
            args.benchmark_repeats,
            comparison["max_abs_diff"],
            comparison["max_rel_diff"],
            args.abs_tolerance,
            args.rel_tolerance,
            str(numeric_within_tolerance).lower(),
            baseline_best,
            optimized_best,
            speedup,
        ),
    )
    if not outputs_match:
        print(
            f"[E2E-GEN] {case_name}: output mismatch "
            f"max_abs_diff={comparison['max_abs_diff']} "
            f"max_rel_diff={comparison['max_rel_diff']}"
        )
        return 1

    effect_contracts = (
        len(args.optimized_loop_needle)
        + int(args.require_optimized_loop_differs_from_cached)
        + int(args.require_parallelized)
        + int(args.require_vectorized)
    )
    print(
        f"[E2E-GEN] PASS case={case_name} "
        "expected=outputs-match"
        f",parallel={str(args.require_parallelized).lower()}"
        f",vector={str(args.require_vectorized).lower()}"
        f",effect-contracts={effect_contracts} "
        f"actual=outputs-match:{str(outputs_match).lower()}"
        f",parallel:{str(parallelized_loop).lower()}"
        f",vector:{str(vectorized_loop).lower()}"
        f",effects-matched:{'true' if effect_contracts else 'not-applicable'}"
        f",omp-threads-requested:{args.omp_threads} "
        f"executions={args.benchmark_repeats} "
        f"coverage={'effect-and-executable-semantics' if effect_contracts else 'executable-semantics'} "
        "interpretation="
        + (
            "requested-effects-occurred-and-generated-executions-agree"
            if effect_contracts
            else "generated-baseline-and-optimized-execution-agree"
        )
    )
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
