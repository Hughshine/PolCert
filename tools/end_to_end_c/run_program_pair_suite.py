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


ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNNER = pathlib.Path(__file__).resolve().with_name("run_generated_case.py")


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
        "--timeout-seconds",
        str(timeout_seconds),
        "--benchmark-repeats",
        str(repeats),
        "--omp-threads",
        str(omp_threads),
    ]
    proc = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=timeout_seconds * 3 + 30,
        check=False,
    )
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
    record: dict[str, object] = {
        "suite": pair["suite"],
        "case": pair["case"],
        "pair_id": pair_id,
        "result": summary["result"],
        "outputs_match": summary["outputs_match"],
        "exact_match": summary["exact_match"],
        "numeric_finite": summary["numeric_finite"],
        "numeric_within_tolerance": summary["numeric_within_tolerance"],
        "max_abs_diff": summary["max_abs_diff"],
        "max_rel_diff": summary["max_rel_diff"],
        "baseline_output": baseline_output.rstrip("\n"),
        "optimized_output": optimized_output.rstrip("\n"),
        "params": summary["params"],
        "omp_threads_requested": summary["omp_threads_requested"],
        "execution_repeats": summary["execution_repeats"],
        "parallelized_loop": summary["parallelized_loop"],
        "vectorized_loop": summary["vectorized_loop"],
        "summary": f"{pair_id}/summary.json",
        "baseline_stdout": f"{pair_id}/baseline.stdout.txt",
        "optimized_stdout": f"{pair_id}/optimized.stdout.txt",
    }
    for path in result_dir.iterdir():
        if path.name not in {
            "summary.json",
            "status.txt",
            "baseline.stdout.txt",
            "optimized.stdout.txt",
        }:
            path.unlink()
    return record


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Execute every accepted Loop pair saved by the test artifact."
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

    with tempfile.TemporaryDirectory(prefix="polcert-pair-execution-") as tmp:
        staging_root = pathlib.Path(tmp)
        results: list[dict[str, object]] = []
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {
                executor.submit(
                    run_pair,
                    pair,
                    pairs_root=pairs_root,
                    output_root=output_root,
                    staging_root=staging_root,
                    timeout_seconds=args.timeout_seconds,
                    omp_threads=args.omp_threads,
                ): pair
                for pair in pairs
            }
            for future in as_completed(futures):
                result = future.result()
                results.append(result)
                print(
                    "[PAIR-EXEC] {} suite={} case={} baseline={} optimized={} "
                    "exact={} repeats={}".format(
                        str(result["result"]).upper(),
                        result["suite"],
                        result["case"],
                        result.get("baseline_output", "unavailable"),
                        result.get("optimized_output", "unavailable"),
                        str(result.get("exact_match", False)).lower(),
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
        "matched_pairs": len(results) - len(failures),
        "failed_pairs": len(failures),
        "integer_control_semantics": "Rocq Z.div and Z.mod",
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
        "coverage=all-accepted-Loop-pairs "
        "interpretation=every-saved-Loop-pair-executed-with-matching-output"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
