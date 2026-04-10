#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[2]


def load_json(path: pathlib.Path) -> dict:
    return json.loads(path.read_text())


def run_candidate(
    runner: pathlib.Path,
    case_dir: pathlib.Path,
    output_root: str,
    tier: str,
    param_config: str,
    benchmark_repeats: int,
    timeout_seconds: int,
    polopt: str | None,
    pipeline_name: str,
    spec: dict,
) -> pathlib.Path:
    cmd = [
        sys.executable,
        str(runner),
        str(case_dir),
        "--pipeline-name",
        pipeline_name,
        "--output-root",
        output_root,
        "--benchmark-repeats",
        str(benchmark_repeats),
        "--timeout-seconds",
        str(timeout_seconds),
        "--omp-threads",
        str(spec.get("omp_threads", 1)),
        "--tier",
        tier,
        "--param-config",
        param_config,
    ]
    source = spec.get("source", "cached_default_no_iss_affine_tiling")
    if source == "input":
        cmd.append("--use-input-loop-as-optimized")
    elif source == "polopt":
        if not polopt:
            raise SystemExit(f"pipeline {pipeline_name} requires --polopt")
        cmd.extend(["--polopt", polopt])
        for arg in spec.get("polopt_args", []):
            cmd.append(f"--polopt-arg={arg}")
        if spec.get("require_parallelized", False):
            cmd.append("--require-parallelized")

    subprocess.run(cmd, cwd=str(ROOT), check=False, text=True)
    return (ROOT / output_root / case_dir.name / "summary.json").resolve()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases-root", default="tests/polopt-generated/cases")
    ap.add_argument("--polopt")
    ap.add_argument("--pipeline-config", default="tests/end-to-end-generated/pipeline_candidates.json")
    ap.add_argument("--output-root", default="tests/end-to-end-generated/search")
    ap.add_argument("--summary-out", default="tests/end-to-end-generated/best_pipelines.json")
    ap.add_argument("--report-out", default="tests/end-to-end-generated/best_pipeline_report.json")
    ap.add_argument("--benchmark-repeats", type=int, default=1)
    ap.add_argument("--timeout-seconds", type=int, default=300)
    ap.add_argument("--tier", default="perf")
    ap.add_argument("--param-config", default="tests/end-to-end-generated/param_tiers.json")
    ap.add_argument("cases", nargs="*")
    args = ap.parse_args()

    runner = (ROOT / "tools/end_to_end_c/run_generated_case.py").resolve()
    cfg = load_json((ROOT / args.pipeline_config).resolve())
    pipelines = {entry["name"]: entry for entry in cfg["pipelines"]}
    default_pipeline = cfg["default_pipeline"]

    cases_root = (ROOT / args.cases_root).resolve()
    if args.cases:
        case_dirs = [cases_root / name for name in args.cases]
    else:
        case_dirs = sorted(path for path in cases_root.iterdir() if path.is_dir())

    report: dict[str, dict] = {}
    chosen: dict[str, str] = {}
    for case_dir in case_dirs:
        case_name = case_dir.name
        entries: list[dict] = []
        successful: list[dict] = []
        for pipeline_name, spec in pipelines.items():
            summary_path = run_candidate(
                runner=runner,
                case_dir=case_dir,
                output_root=f"{args.output_root}/{pipeline_name}",
                tier=args.tier,
                param_config=args.param_config,
                benchmark_repeats=args.benchmark_repeats,
                timeout_seconds=args.timeout_seconds,
                polopt=args.polopt,
                pipeline_name=pipeline_name,
                spec=spec,
            )
            if summary_path.exists():
                data = load_json(summary_path)
            else:
                data = {"result": "missing_summary"}
            data["pipeline_name"] = pipeline_name
            entries.append(data)
            if data.get("result") == "ok":
                successful.append(data)
        preferred = [
            data
            for data in successful
            if data["pipeline_name"] != "identity" and float(data.get("speedup", 0.0)) > 1.0
        ]
        if preferred:
            best = min(preferred, key=lambda data: float(data.get("optimized_best_seconds", float("inf"))))
        elif successful:
            best = max(successful, key=lambda data: float(data.get("speedup", 0.0)))
        else:
            best = None
        chosen[case_name] = best["pipeline_name"] if best else default_pipeline
        report[case_name] = {
            "best_pipeline": chosen[case_name],
            "best_speedup": float(best.get("speedup", -1.0)) if best else -1.0,
            "best_optimized_best_seconds": (
                float(best.get("optimized_best_seconds", -1.0)) if best else -1.0
            ),
            "candidates": entries,
        }

    summary = {
        "default_pipeline": default_pipeline,
        "pipelines": cfg["pipelines"],
        "cases": chosen,
    }
    (ROOT / args.summary_out).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    (ROOT / args.report_out).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(
        "[E2E-GEN-SEARCH] OK cases={} summary={}".format(
            len(case_dirs),
            args.summary_out,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
