#!/usr/bin/env python3
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile

from generated_harness import build_harness, load_param_tiers


ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNNER = pathlib.Path(__file__).resolve().with_name("run_generated_case.py")
PARAM_CONFIG = ROOT / "tests/end-to-end-generated/param_tiers.json"


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be greater than zero")
    return parsed


def pair_path(root: pathlib.Path, value: str) -> pathlib.Path:
    path = (root / value).resolve()
    if not path.is_file():
        raise ValueError(f"missing program-pair file: {path}")
    return path


def is_executable_loop_pair(pair: dict[str, object]) -> bool:
    return (
        pair.get("kind", "accepted-program-pair") == "accepted-program-pair"
        and pathlib.Path(str(pair["before"])).suffix == ".loop"
        and pathlib.Path(str(pair["after"])).suffix == ".loop"
    )


def execution_configuration(
    pair: dict[str, object],
    *,
    pairs_root: pathlib.Path,
    tier_overrides: dict[str, dict[str, dict[str, int]]],
    omp_threads: int,
) -> tuple[str, str, str, int, int]:
    before_text = pair_path(pairs_root, str(pair["before"])).read_text(encoding="utf-8")
    after_text = pair_path(pairs_root, str(pair["after"])).read_text(encoding="utf-8")
    info = build_harness(
        str(pair["case"]),
        before_text,
        after_text,
        tier_overrides=tier_overrides,
    )
    repeats = 3 if "parallel for " in after_text else 1
    return (
        before_text,
        after_text,
        json.dumps(info.params, sort_keys=True),
        repeats,
        omp_threads,
    )


def materialize_pair_result(
    base: dict[str, object],
    pair: dict[str, object],
    *,
    pairs_root: pathlib.Path,
    output_root: pathlib.Path,
) -> dict[str, object]:
    pair_id = pair_path(pairs_root, str(pair["before"])).parent.name
    record = {
        **base,
        "suite": pair["suite"],
        "case": pair["case"],
        "pair_id": pair_id,
    }
    if record["result"] != "ok":
        return record
    source_dir = output_root / str(base["pair_id"])
    target_dir = output_root / pair_id
    if target_dir != source_dir:
        target_dir.mkdir()
        for name in (
            "status.txt",
            "baseline.observation.txt",
            "optimized.observation.txt",
        ):
            shutil.copy2(source_dir / name, target_dir / name)
    record.update(
        {
            "summary": f"{pair_id}/summary.json",
            "baseline_observation": f"{pair_id}/baseline.observation.txt",
            "optimized_observation": f"{pair_id}/optimized.observation.txt",
        }
    )
    (target_dir / "summary.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return record


def run_pair(
    pair: dict[str, object],
    *,
    pairs_root: pathlib.Path,
    output_root: pathlib.Path,
    staging_root: pathlib.Path,
    timeout_seconds: int,
    omp_threads: int,
) -> dict[str, object]:
    before = pair_path(pairs_root, str(pair["before"]))
    after = pair_path(pairs_root, str(pair["after"]))
    pair_id = before.parent.name
    case_dir = staging_root / pair_id
    case_dir.mkdir()
    shutil.copy2(before, case_dir / "input.loop")
    shutil.copy2(after, case_dir / "optimized.loop")
    after_text = after.read_text(encoding="utf-8")
    repeats = 3 if "parallel for " in after_text else 1
    command = [
        sys.executable,
        str(RUNNER),
        str(case_dir),
        "--output-root",
        str(output_root),
        "--harness-case-name",
        str(pair["case"]),
        "--state-digest-output",
        "--timeout-seconds",
        str(timeout_seconds),
        "--benchmark-repeats",
        str(repeats),
        "--omp-threads",
        str(omp_threads),
    ]
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=timeout_seconds * (2 * repeats) + 60,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        return {
            "suite": pair["suite"],
            "case": pair["case"],
            "pair_id": pair_id,
            "result": "fail",
            "runner_exit": "timeout",
            "runner_stdout": (error.stdout or "")[-4000:],
            "runner_stderr": (error.stderr or "")[-4000:],
        }
    result_dir = output_root / pair_id
    summary_path = result_dir / "summary.json"
    if proc.returncode != 0 or not summary_path.is_file():
        return {
            "suite": pair["suite"],
            "case": pair["case"],
            "pair_id": pair_id,
            "result": "fail",
            "runner_exit": proc.returncode,
            "runner_stdout": proc.stdout[-4000:],
            "runner_stderr": proc.stderr[-4000:],
        }

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    baseline_output = (result_dir / "baseline.stdout.txt").read_text(encoding="utf-8")
    optimized_output = (result_dir / "optimized.stdout.txt").read_text(encoding="utf-8")
    baseline_sha256 = summary["baseline_output_sha256"]
    optimized_sha256 = summary["optimized_output_sha256"]
    strict_match = (
        summary["result"] == "ok"
        and summary["outputs_match"] is True
        and summary["exact_match"] is True
        and summary["numeric_finite"] is True
        and summary["observation_mode"] == "sha256-modeled-state"
        and int(summary["observed_value_count"]) > 0
        and baseline_sha256 == optimized_sha256
    )
    record: dict[str, object] = {
        "suite": pair["suite"],
        "case": pair["case"],
        "pair_id": pair_id,
        "result": "ok" if strict_match else "fail",
        "outputs_match": strict_match,
        "exact_match": summary["exact_match"],
        "numeric_finite": summary["numeric_finite"],
        "numeric_within_tolerance": summary["numeric_within_tolerance"],
        "max_abs_diff": summary["max_abs_diff"],
        "max_rel_diff": summary["max_rel_diff"],
        "observation_mode": summary["observation_mode"],
        "observed_value_count": summary["observed_value_count"],
        "baseline_output_sha256": baseline_sha256,
        "optimized_output_sha256": optimized_sha256,
        "params": summary["params"],
        "omp_threads_requested": summary["omp_threads_requested"],
        "execution_repeats": summary["execution_repeats"],
        "parallelized_loop": summary["parallelized_loop"],
        "vectorized_loop": summary["vectorized_loop"],
        "summary": f"{pair_id}/summary.json",
        "baseline_observation": f"{pair_id}/baseline.observation.txt",
        "optimized_observation": f"{pair_id}/optimized.observation.txt",
    }
    (result_dir / "baseline.observation.txt").write_text(
        baseline_output, encoding="utf-8"
    )
    (result_dir / "optimized.observation.txt").write_text(
        optimized_output, encoding="utf-8"
    )
    for path in result_dir.iterdir():
        if path.name not in {
            "summary.json",
            "status.txt",
            "baseline.observation.txt",
            "optimized.observation.txt",
        }:
            path.unlink()
    return record


def main() -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Cover every accepted Loop-pair record by executing each unique "
            "program and parameter configuration."
        )
    )
    ap.add_argument("--index", type=pathlib.Path, required=True)
    ap.add_argument("--pairs-root", type=pathlib.Path, required=True)
    ap.add_argument("--output-root", type=pathlib.Path, required=True)
    ap.add_argument(
        "--jobs",
        type=positive_int,
        default=max(1, min(8, os.cpu_count() or 1)),
    )
    ap.add_argument("--timeout-seconds", type=positive_int, default=60)
    ap.add_argument("--omp-threads", type=positive_int, default=4)
    args = ap.parse_args()

    index_path = args.index.resolve()
    pairs_root = args.pairs_root.resolve()
    output_root = args.output_root.resolve()
    if output_root.exists():
        shutil.rmtree(output_root)
    output_root.mkdir(parents=True)

    data = json.loads(index_path.read_text(encoding="utf-8"))
    pairs = [pair for pair in data["pairs"] if is_executable_loop_pair(pair)]
    if not pairs:
        raise SystemExit("no accepted Loop pairs in the supplied index")

    tier_overrides = load_param_tiers(PARAM_CONFIG)
    grouped: dict[tuple[str, str, str, int, int], list[dict[str, object]]] = {}
    for pair in pairs:
        key = execution_configuration(
            pair,
            pairs_root=pairs_root,
            tier_overrides=tier_overrides,
            omp_threads=args.omp_threads,
        )
        grouped.setdefault(key, []).append(pair)

    worker_count = min(
        args.jobs, max(1, (os.cpu_count() or 1) // args.omp_threads)
    )
    with tempfile.TemporaryDirectory(prefix="polcert-pair-execution-") as tmp:
        staging_root = pathlib.Path(tmp)
        results: list[dict[str, object]] = []
        executed_configurations = 0
        with ThreadPoolExecutor(max_workers=worker_count) as executor:
            futures = {
                executor.submit(
                    run_pair,
                    grouped_pairs[0],
                    pairs_root=pairs_root,
                    output_root=output_root,
                    staging_root=staging_root,
                    timeout_seconds=args.timeout_seconds,
                    omp_threads=args.omp_threads,
                ): grouped_pairs
                for grouped_pairs in grouped.values()
            }
            for future in as_completed(futures):
                base_result = future.result()
                executed_configurations += 1
                for pair in futures[future]:
                    result = materialize_pair_result(
                        base_result,
                        pair,
                        pairs_root=pairs_root,
                        output_root=output_root,
                    )
                    results.append(result)
                    print(
                        "[PAIR-EXEC] {} suite={} case={} baseline={} optimized={} "
                        "digest_match={} repeats={}".format(
                            str(result["result"]).upper(),
                            result["suite"],
                            result["case"],
                            str(result.get("baseline_output_sha256", "unavailable"))[:12],
                            str(result.get("optimized_output_sha256", "unavailable"))[:12],
                            str(result.get("outputs_match", False)).lower(),
                            result.get("execution_repeats", 0),
                        ),
                        flush=True,
                    )

    results.sort(key=lambda item: (str(item["suite"]), str(item["case"])))
    failures = [result for result in results if result["result"] != "ok"]
    manifest = {
        "schema": 1,
        "eligible_pairs": len(pairs),
        "executed_pairs": len(results),
        "unique_execution_configurations": len(grouped),
        "executed_configurations": executed_configurations,
        "worker_count": worker_count,
        "matched_pairs": len(results) - len(failures),
        "failed_pairs": len(failures),
        "integer_control_semantics": "Rocq Z.div and Z.mod over tested signed 64-bit values",
        "state_observation": "SHA-256 over every finite modeled scalar and array value",
        "results": results,
    }
    (output_root / "index.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if failures:
        print(
            f"[PAIR-EXEC-SUITE] FAIL expected={len(pairs)} actual={len(results) - len(failures)}",
            file=sys.stderr,
        )
        for result in failures:
            print(
                f"  - {result['suite']}/{result['case']}: "
                f"{result.get('runner_stderr') or result.get('runner_stdout')}",
                file=sys.stderr,
            )
        return 1
    print(
        f"[PAIR-EXEC-SUITE] PASS expected={len(pairs)} actual={len(results)} "
        f"unique-configurations={len(grouped)} "
        "coverage=all-accepted-Loop-pair-records "
        "interpretation=every-record-has-a-matching-modeled-state-digest"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
