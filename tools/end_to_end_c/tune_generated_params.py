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

from generated_harness import DEFAULT_TIER, build_harness, load_param_tiers, render_program_source
from run_case import compile_c, write_text


ROOT = pathlib.Path(__file__).resolve().parents[2]
FACTOR_CANDIDATES = {
    1: [1, 2, 4, 8, 16, 32, 64],
    2: [1, 2, 4, 8, 16, 32, 64, 128, 256],
    3: [1, 2, 4, 8, 16, 32],
    4: [1, 2, 4, 8, 12, 16, 24, 32],
}


def param_rank(input_loop: str) -> int:
    return max(input_loop.count("[") // max(input_loop.count("\n"), 1), 0)


def max_array_rank(loop_text: str) -> int:
    rank = 0
    i = 0
    while i < len(loop_text):
        if loop_text[i].isalpha() or loop_text[i] == "_":
            j = i + 1
            while j < len(loop_text) and (loop_text[j].isalnum() or loop_text[j] == "_"):
                j += 1
            k = j
            current = 0
            while k < len(loop_text) and loop_text[k] == "[":
                current += 1
                depth = 1
                k += 1
                while k < len(loop_text) and depth > 0:
                    if loop_text[k] == "[":
                        depth += 1
                    elif loop_text[k] == "]":
                        depth -= 1
                    k += 1
            rank = max(rank, current)
            i = k
        else:
            i += 1
    return rank


def scale_params(params: dict[str, int], factor: int) -> dict[str, int]:
    return {name: max(1, int(value * factor)) for name, value in params.items()}


def load_case(case_dir: pathlib.Path) -> tuple[str, str]:
    return (case_dir / "input.loop").read_text(), (case_dir / "optimized.loop").read_text()


def measure_case(
    case_dir: pathlib.Path,
    params: dict[str, int],
    *,
    tier_overrides,
    trial_timeout_seconds: float,
) -> tuple[float, bool]:
    input_loop, optimized_loop = load_case(case_dir)
    scratch = (ROOT / "tests/end-to-end-generated/out-tuning" / case_dir.name).resolve()
    if scratch.exists():
        shutil.rmtree(scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    overrides = dict(tier_overrides)
    case_entry = dict(overrides.get(case_dir.name, {}))
    case_entry[DEFAULT_TIER] = params
    overrides[case_dir.name] = case_entry
    info = build_harness(
        case_dir.name,
        input_loop,
        optimized_loop,
        tier=DEFAULT_TIER,
        tier_overrides=overrides,
    )
    src = scratch / "baseline.c"
    exe = scratch / "baseline.exe"
    write_text(src, render_program_source(info, optimized=False))
    build = compile_c(src, exe, openmp=info.openmp)
    if build.returncode != 0:
        return 0.0, False
    env = dict(**os.environ)
    env.setdefault("OMP_NUM_THREADS", "1")
    started = time.perf_counter()
    try:
        proc = subprocess.run(
            [str(exe)],
            text=True,
            capture_output=True,
            env=env,
            timeout=trial_timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return 0.0, False
    elapsed = time.perf_counter() - started
    if proc.returncode != 0:
        return 0.0, False
    return elapsed, True


def choose_factors(rank: int) -> list[int]:
    return FACTOR_CANDIDATES.get(rank, [1, 2, 4, 8])


def tune_case(case_dir: pathlib.Path, *, target_seconds: float, max_seconds: float, trial_timeout_seconds: float, tier_overrides):
    input_loop, optimized_loop = load_case(case_dir)
    base_info = build_harness(
        case_dir.name,
        input_loop,
        optimized_loop,
        tier=DEFAULT_TIER,
        tier_overrides=tier_overrides,
    )
    rank = max((len(dims) for dims in base_info.arrays.values()), default=0)
    factors = choose_factors(rank)
    perf_params = base_info.params
    perf_time = 0.0
    heavy_params = base_info.params
    heavy_time = 0.0
    for factor in factors:
        candidate = scale_params(base_info.params, factor)
        elapsed, ok = measure_case(
            case_dir,
            candidate,
            tier_overrides=tier_overrides,
            trial_timeout_seconds=trial_timeout_seconds,
        )
        if not ok:
            break
        perf_params = candidate
        perf_time = elapsed
        if elapsed >= target_seconds:
            break
    for factor in [1, 2, 4]:
        candidate = scale_params(perf_params, factor)
        elapsed, ok = measure_case(
            case_dir,
            candidate,
            tier_overrides=tier_overrides,
            trial_timeout_seconds=trial_timeout_seconds,
        )
        if not ok or elapsed > max_seconds:
            break
        heavy_params = candidate
        heavy_time = elapsed
    return {
        "rank": rank,
        "smoke": base_info.params,
        "perf": perf_params,
        "heavy": heavy_params,
        "perf_seconds": perf_time,
        "heavy_seconds": heavy_time,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases-root", default="tests/polopt-generated/cases")
    ap.add_argument("--param-config", default="tests/end-to-end-generated/param_tiers.json")
    ap.add_argument("--target-seconds", type=float, default=2.0)
    ap.add_argument("--max-seconds", type=float, default=12.0)
    ap.add_argument("--trial-timeout-seconds", type=float, default=20.0)
    ap.add_argument("cases", nargs="*")
    args = ap.parse_args()

    cases_root = (ROOT / args.cases_root).resolve()
    config_path = (ROOT / args.param_config).resolve()
    tier_overrides = load_param_tiers(config_path)
    case_dirs = [cases_root / name for name in args.cases] if args.cases else sorted(p for p in cases_root.iterdir() if p.is_dir())
    out: dict[str, dict[str, dict[str, int]]] = {}
    for case_dir in case_dirs:
        tuned = tune_case(
            case_dir,
            target_seconds=args.target_seconds,
            max_seconds=args.max_seconds,
            trial_timeout_seconds=args.trial_timeout_seconds,
            tier_overrides=tier_overrides,
        )
        out[case_dir.name] = {
            "smoke": tuned["smoke"],
            "perf": tuned["perf"],
            "heavy": tuned["heavy"],
        }
        print(
            f"{case_dir.name} rank={tuned['rank']} "
            f"perf={tuned['perf']} perf_seconds={tuned['perf_seconds']:.3f} "
            f"heavy={tuned['heavy']} heavy_seconds={tuned['heavy_seconds']:.3f}"
        , flush=True)
    write_text(config_path, json.dumps(out, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
