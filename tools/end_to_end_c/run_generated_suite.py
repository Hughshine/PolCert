#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys

from generated_harness import DEFAULT_TIER


ROOT = pathlib.Path(__file__).resolve().parents[2]


def load_pipeline_config(path: pathlib.Path) -> dict:
    data = json.loads(path.read_text())
    pipelines = {entry["name"]: entry for entry in data.get("pipelines", [])}
    default_name = data.get("default_pipeline")
    case_map = data.get("cases", {})
    return {
        "pipelines": pipelines,
        "default_pipeline": default_name,
        "cases": case_map,
    }


def resolve_pipeline_name(case_name: str, cfg: dict | None, explicit_default: str | None) -> str | None:
    if not cfg:
        return None
    if case_name in cfg["cases"]:
        return cfg["cases"][case_name]
    if explicit_default:
        return explicit_default
    return cfg.get("default_pipeline")


def pipeline_requires_parallelized(spec: dict) -> bool:
    if spec.get("require_parallelized", False):
        return True
    return "--parallel" in spec.get("polopt_args", [])


def append_pipeline_args(cmd: list[str], spec: dict, polopt: str | None, require_parallelized: bool) -> None:
    source = spec.get("source", "cached_default_no_iss_affine_tiling")
    if source == "input":
        cmd.append("--use-input-loop-as-optimized")
    elif source == "polopt":
        if not polopt:
            raise SystemExit(f"pipeline {spec['name']} requires --polopt")
        cmd.extend(["--polopt", polopt])
        for arg in spec.get("polopt_args", []):
            cmd.append(f"--polopt-arg={arg}")
        if require_parallelized or pipeline_requires_parallelized(spec):
            cmd.append("--require-parallelized")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases-root", default="tests/polopt-generated/cases")
    ap.add_argument("--polopt")
    ap.add_argument("--polopt-arg", action="append", default=[])
    ap.add_argument("--output-root", default="tests/end-to-end-generated/out")
    ap.add_argument("--pipeline-config")
    ap.add_argument("--default-pipeline")
    ap.add_argument("--benchmark-repeats", type=int, default=1)
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--omp-threads", type=int, default=1)
    ap.add_argument("--require-parallelized", action="store_true")
    ap.add_argument("--abs-tolerance", type=float)
    ap.add_argument("--rel-tolerance", type=float)
    ap.add_argument("--tier", default=DEFAULT_TIER)
    ap.add_argument(
        "--param-config",
        default="tests/end-to-end-generated/param_tiers.json",
    )
    ap.add_argument("cases", nargs="*")
    args = ap.parse_args()

    cases_root = (ROOT / args.cases_root).resolve()
    runner = (ROOT / "tools/end_to_end_c/run_generated_case.py").resolve()
    pipeline_cfg = load_pipeline_config((ROOT / args.pipeline_config).resolve()) if args.pipeline_config else None
    if args.cases:
        case_dirs = [cases_root / name for name in args.cases]
    else:
        case_dirs = sorted(path for path in cases_root.iterdir() if path.is_dir())

    failed: list[str] = []
    for case_dir in case_dirs:
        cmd = [
            sys.executable,
            str(runner),
            str(case_dir),
            "--output-root",
            args.output_root,
            "--benchmark-repeats",
            str(args.benchmark_repeats),
            "--timeout-seconds",
            str(args.timeout_seconds),
            "--omp-threads",
            str(args.omp_threads),
            "--tier",
            args.tier,
            "--param-config",
            args.param_config,
        ]
        if args.abs_tolerance is not None:
            cmd.extend(["--abs-tolerance", str(args.abs_tolerance)])
        if args.rel_tolerance is not None:
            cmd.extend(["--rel-tolerance", str(args.rel_tolerance)])
        pipeline_name = resolve_pipeline_name(case_dir.name, pipeline_cfg, args.default_pipeline)
        if pipeline_name:
            spec = pipeline_cfg["pipelines"][pipeline_name]
            cmd.extend(["--pipeline-name", pipeline_name])
            cmd.extend(["--omp-threads", str(spec.get("omp_threads", args.omp_threads))])
            append_pipeline_args(cmd, spec, args.polopt, args.require_parallelized)
        else:
            if args.polopt:
                cmd.extend(["--polopt", args.polopt])
                for arg in args.polopt_arg:
                    cmd.append(f"--polopt-arg={arg}")
                if args.require_parallelized:
                    cmd.append("--require-parallelized")
        proc = subprocess.run(
            cmd,
            cwd=str(ROOT),
            text=True,
        )
        if proc.returncode != 0:
            failed.append(case_dir.name)

    if failed:
        print("[E2E-GEN-SUITE] FAIL")
        for name in failed:
            print(f"  - {name}")
        return 1

    print(f"[E2E-GEN-SUITE] OK cases={len(case_dirs)}")
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
    raise SystemExit(main())
