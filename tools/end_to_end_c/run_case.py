#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import pathlib
import subprocess
import sys

from loop_to_c import INTEGER_HELPERS_C, transpile_loop_text
from runner_common import (
    ROOT,
    compile_c,
    evaluate_outputs,
    extract_optimized_loop,
    fail_run,
    has_parallel_loop,
    has_vector_loop,
    loop_requires_openmp,
    recreate_dir,
    run,
    timed_run,
    write_text,
)

KERNEL_MARKER = "/* POLCERT_KERNEL */"


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return parsed


def render_source(template: str, kernel_c: str) -> str:
    if KERNEL_MARKER not in template:
        raise ValueError(f"missing kernel marker {KERNEL_MARKER!r}")
    main_marker = "int main(void) {"
    if main_marker not in template:
        raise ValueError(f"missing C entry point {main_marker!r}")
    with_runtime = (
        template
        if "#include <stdlib.h>" in template
        else "#include <stdlib.h>\n" + template
    )
    with_helpers = with_runtime.replace(
        main_marker, f"{INTEGER_HELPERS_C}\n{main_marker}", 1
    )
    return with_helpers.replace(KERNEL_MARKER, kernel_c.rstrip())


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


def str_dict_from_meta(meta: dict[str, object], key: str) -> dict[str, str]:
    value = meta.get(key, {})
    if not isinstance(value, dict):
        raise ValueError(f"{key} must be a string dictionary")
    result: dict[str, str] = {}
    for item_key, item_value in value.items():
        if not isinstance(item_key, str) or not isinstance(item_value, str):
            raise ValueError(f"{key} must be a string dictionary")
        result[item_key] = item_value
    return result


def require_markers(loop_text: str, markers: list[str], *, present: bool) -> str | None:
    for marker in markers:
        found = marker in loop_text
        if present and not found:
            return f"missing optimized-loop marker: {marker}"
        if not present and found:
            return f"unexpected optimized-loop marker: {marker}"
    return None


def float_from_meta(meta: dict[str, object], key: str, default: float = 0.0) -> float:
    value = meta.get(key, default)
    if not isinstance(value, (int, float)):
        raise ValueError(f"{key} must be numeric")
    return float(value)


def has_loop_header(loop_text: str) -> bool:
    for line in loop_text.splitlines():
        stripped = line.strip()
        if (
            stripped.startswith("for ")
            or stripped.startswith("parallel for ")
            or stripped.startswith("vector for ")
        ):
            return True
    return False


def select_failure_diagnostic(*texts: str) -> str:
    lines = [line.strip() for text in texts for line in text.splitlines() if line.strip()]
    for predicate in (
        lambda line: "status=rejected" in line,
        lambda line: line.startswith("[alarm]"),
        lambda line: "error" in line.lower() or "fail" in line.lower(),
    ):
        for line in reversed(lines):
            if predicate(line):
                return line
    return lines[-1] if lines else "none"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("case_dir")
    ap.add_argument("--polopt", default="./polopt")
    ap.add_argument("--polopt-arg", action="append", default=[])
    ap.add_argument("--output-root", default="tests/end-to-end-c/out")
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--benchmark-repeats", type=positive_int, default=3)
    ap.add_argument("--execution-repeats", type=positive_int)
    ap.add_argument("--omp-threads", type=positive_int, default=1)
    ap.add_argument("--require-parallelized", action="store_true")
    ap.add_argument("--require-vectorized", action="store_true")
    ap.add_argument("--keep-going", action="store_true")
    args = ap.parse_args()

    case_dir = pathlib.Path(args.case_dir).resolve()
    meta = load_meta(case_dir)
    case_name = case_dir.name
    out_dir = (ROOT / args.output_root / case_name).resolve()
    recreate_dir(out_dir)

    loop_path = (case_dir / meta["loop"]).resolve()
    template_path = (case_dir / "wrapper.c.in").resolve()
    polopt = pathlib.Path(args.polopt).resolve()
    polopt_args = list_from_meta(meta, "polopt_args")
    benchmark = bool_from_meta(meta, "benchmark", default=True)
    openmp = bool_from_meta(meta, "openmp", default=False)
    require_unrolled = bool_from_meta(meta, "require_unrolled", default=False)
    require_parallelized = args.require_parallelized or bool_from_meta(
        meta, "require_parallelized", default=False
    )
    require_vectorized = args.require_vectorized or bool_from_meta(
        meta, "require_vectorized", default=False
    )
    abs_tolerance = float_from_meta(meta, "abs_tolerance", default=0.0)
    rel_tolerance = float_from_meta(meta, "rel_tolerance", default=0.0)
    meta_execution_repeats = meta.get("execution_repeats")
    if meta_execution_repeats is not None and (
        not isinstance(meta_execution_repeats, int) or meta_execution_repeats <= 0
    ):
        raise ValueError("execution_repeats must be a positive integer")
    execution_repeats = (
        args.execution_repeats
        or meta_execution_repeats
        or (args.benchmark_repeats if benchmark else 1)
    )

    template = template_path.read_text()
    input_loop = loop_path.read_text()

    write_text(out_dir / "input.loop", input_loop)
    baseline_kernel = transpile_loop_text(input_loop)
    baseline_src = render_source(template, baseline_kernel)
    write_text(out_dir / "baseline.kernel.c", baseline_kernel)
    write_text(out_dir / "baseline.c", baseline_src)

    polopt_cmd = [str(polopt), *polopt_args, *args.polopt_arg, str(loop_path)]
    polopt_env = os.environ.copy()
    polopt_env.setdefault(
        "COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini")
    )
    polopt_env.update(str_dict_from_meta(meta, "polopt_env"))
    try:
        proc = run(polopt_cmd, cwd=ROOT, timeout=args.timeout_seconds, env=polopt_env)
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
        diagnostic = select_failure_diagnostic(proc.stdout, proc.stderr)
        print(
            f"[E2E] FAIL case={case_name} stage=polopt expected=exit:0 "
            f"actual=exit:{proc.returncode} diagnostic={diagnostic!r} "
            "interpretation=scheduler-or-validation-rejected-route",
            file=sys.stderr,
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] polopt failed")

    optimized_loop = extract_optimized_loop(proc.stdout)
    parallelized_loop = has_parallel_loop(optimized_loop)
    vectorized_loop = has_vector_loop(optimized_loop)
    write_text(out_dir / "optimized.loop", optimized_loop)
    marker_error = require_markers(
        optimized_loop,
        list_from_meta(meta, "optimized_loop_needles"),
        present=True,
    )
    if marker_error is None:
        marker_error = require_markers(
            optimized_loop,
            list_from_meta(meta, "optimized_loop_absent"),
            present=False,
        )
    if marker_error is not None:
        write_text(
            out_dir / "status.txt",
            f"result=fail\nstage=optimized-loop-marker\nreason={marker_error}\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] {marker_error}")
    if require_parallelized and not parallelized_loop:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=parallelize\nparallelized_loop=false\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] no parallel for emitted")
    if require_vectorized and not vectorized_loop:
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=vectorize\nvectorized_loop=false\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] no vector for emitted")
    if require_unrolled and has_loop_header(optimized_loop):
        write_text(
            out_dir / "status.txt",
            "result=fail\nstage=unroll\nunrolled_loop=false\n",
        )
        if args.keep_going:
            return 1
        raise SystemExit(f"[{case_name}] loop header remained after required unroll")
    optimized_kernel = transpile_loop_text(optimized_loop)
    optimized_src = render_source(template, optimized_kernel)
    write_text(out_dir / "optimized.kernel.c", optimized_kernel)
    write_text(out_dir / "optimized.c", optimized_src)

    baseline_exe = out_dir / "baseline.exe"
    optimized_exe = out_dir / "optimized.exe"
    compile_with_openmp = (
        openmp
        or loop_requires_openmp(input_loop)
        or loop_requires_openmp(optimized_loop)
    )
    baseline_build = compile_c(
        out_dir / "baseline.c", baseline_exe, openmp=compile_with_openmp
    )
    optimized_build = compile_c(
        out_dir / "optimized.c", optimized_exe, openmp=compile_with_openmp
    )
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
    env["OMP_NUM_THREADS"] = str(args.omp_threads)
    env["OMP_DYNAMIC"] = "FALSE"

    try:
        baseline_stdout, baseline_best = timed_run(
            baseline_exe,
            repeats=execution_repeats,
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
            repeats=execution_repeats,
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
    comparison = evaluate_outputs(
        baseline_stdout,
        optimized_stdout,
        abs_tolerance=abs_tolerance,
        rel_tolerance=rel_tolerance,
    )
    exact_match = bool(comparison["exact_match"])
    numeric_within_tolerance = bool(comparison["numeric_within_tolerance"])
    outputs_match = bool(comparison["outputs_match"])
    speedup = (baseline_best / optimized_best) if optimized_best > 0 else 0.0
    summary = {
        "result": "ok" if outputs_match else "fail",
        "outputs_match": outputs_match,
        "exact_match": exact_match,
        "parallelized_loop": parallelized_loop,
        "vectorized_loop": vectorized_loop,
        "openmp": compile_with_openmp,
        "omp_threads_requested": args.omp_threads,
        "execution_repeats": execution_repeats,
        "numeric_comparable": comparison["numeric_comparable"],
        "numeric_finite": comparison["numeric_finite"],
        "value_count_match": comparison["value_count_match"],
        "max_abs_diff": comparison["max_abs_diff"],
        "max_rel_diff": comparison["max_rel_diff"],
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
        "result={}\noutputs_match={}\nexact_match={}\nparallelized_loop={}\nvectorized_loop={}\nopenmp={}\nomp_threads_requested={}\nexecution_repeats={}\nnumeric_comparable={}\nnumeric_finite={}\nvalue_count_match={}\nmax_abs_diff={}\nmax_rel_diff={}\nabs_tolerance={:.3e}\nrel_tolerance={:.3e}\nnumeric_within_tolerance={}\nbaseline_best_seconds={:.6f}\noptimized_best_seconds={:.6f}\nspeedup={:.4f}\n".format(
            "ok" if outputs_match else "fail",
            str(outputs_match).lower(),
            str(exact_match).lower(),
            str(parallelized_loop).lower(),
            str(vectorized_loop).lower(),
            str(compile_with_openmp).lower(),
            args.omp_threads,
            execution_repeats,
            str(bool(comparison["numeric_comparable"])).lower(),
            str(bool(comparison["numeric_finite"])).lower(),
            str(bool(comparison["value_count_match"])).lower(),
            comparison["max_abs_diff"],
            comparison["max_rel_diff"],
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

    expected_effects = list_from_meta(meta, "optimized_loop_needles")
    forbidden_effects = list_from_meta(meta, "optimized_loop_absent")
    unrolled_loop = not has_loop_header(optimized_loop)
    has_effect_contract = bool(
        expected_effects
        or forbidden_effects
        or require_unrolled
        or require_parallelized
        or require_vectorized
    )
    effect_match = "true" if has_effect_contract else "not-applicable"
    print(
        f"[E2E] PASS case={case_name} "
        "expected=outputs-match"
        f",parallel={str(require_parallelized).lower()}"
        f",vector={str(require_vectorized).lower()}"
        f",unrolled={str(require_unrolled).lower()}"
        f",required-effects={len(expected_effects)}"
        f",forbidden-effects={len(forbidden_effects)} "
        f"coverage={'effect-and-executable-semantics' if has_effect_contract else 'executable-semantics'} "
        f"actual=outputs-match:{str(outputs_match).lower()}"
        f",parallel:{str(parallelized_loop).lower()}"
        f",vector:{str(vectorized_loop).lower()}"
        f",unrolled:{str(unrolled_loop).lower()}"
        f",effects-matched:{effect_match},omp-threads-requested:{args.omp_threads} "
        f"executions={execution_repeats} "
        "interpretation="
        + (
            "required-optimization-effects-occurred-and-optimized-execution-agrees-with-baseline"
            if has_effect_contract
            else "route-succeeded-and-optimized-execution-agrees-with-baseline-no-specific-effect-asserted"
        )
    )
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
