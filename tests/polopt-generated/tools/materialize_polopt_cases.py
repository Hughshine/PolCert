#!/usr/bin/env python3
from __future__ import annotations

import argparse
import difflib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import time

INPUT_MARKER = "== Input Loop ==\n"
OPT_MARKER = "== Optimized Loop ==\n"


def text_or_empty(data: str | bytes | None) -> str:
    if data is None:
        return ""
    if isinstance(data, bytes):
        return data.decode("utf-8", errors="replace")
    return data


def extract_section(stdout: str, marker: str) -> str:
    start = stdout.find(marker)
    if start < 0:
        raise ValueError(f"missing marker {marker!r}")
    start += len(marker)
    end = stdout.find("\n== ", start)
    if end < 0:
        end = len(stdout)
    return stdout[start:end].strip() + "\n"


def load_manifest(path: pathlib.Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"manifest must be a JSON object: {path}")
    return data


def run_case(
    polopt: pathlib.Path,
    polopt_args: list[str],
    src: pathlib.Path,
    out_dir: pathlib.Path,
    timeout_seconds: int,
) -> dict[str, str]:
    out_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, out_dir / "input.loop")
    started = time.perf_counter()

    try:
        proc = subprocess.run(
            [str(polopt), *polopt_args, "--dump-input", str(src)],
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        stderr = text_or_empty(exc.stderr)
        stdout = text_or_empty(exc.stdout)
        if stderr:
            (out_dir / "stderr.txt").write_text(stderr)
        if stdout:
            (out_dir / "stdout.txt").write_text(stdout)
        (out_dir / "status.txt").write_text(
            f"exit_code=timeout\nresult=fail\nreason=timeout({timeout_seconds}s)\n"
        )
        return {
            "result": "fail",
            "reason": f"timeout({timeout_seconds}s)",
            "elapsed_seconds": f"{time.perf_counter() - started:.2f}",
        }

    status_lines = [f"exit_code={proc.returncode}"]
    if proc.returncode != 0:
        status_lines.append("result=fail")
        if proc.stderr:
            (out_dir / "stderr.txt").write_text(proc.stderr)
        (out_dir / "status.txt").write_text("\n".join(status_lines) + "\n")
        return {
            "result": "fail",
            "reason": f"exit({proc.returncode})",
            "elapsed_seconds": f"{time.perf_counter() - started:.2f}",
        }

    input_pretty = extract_section(proc.stdout, INPUT_MARKER)
    optimized = extract_section(proc.stdout, OPT_MARKER)
    changed = input_pretty != optimized

    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "input.pretty.loop").write_text(input_pretty)
    (out_dir / "optimized.loop").write_text(optimized)
    diff = "".join(
        difflib.unified_diff(
            input_pretty.splitlines(keepends=True),
            optimized.splitlines(keepends=True),
            fromfile="input.pretty.loop",
            tofile="optimized.loop",
        )
    )
    (out_dir / "diff.patch").write_text(diff)

    status_lines.extend(
        [
            "result=ok",
            f"changed={'true' if changed else 'false'}",
        ]
    )
    (out_dir / "status.txt").write_text("\n".join(status_lines) + "\n")
    return {
        "result": "ok",
        "changed": "true" if changed else "false",
        "elapsed_seconds": f"{time.perf_counter() - started:.2f}",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest",
        default=None,
        help="JSON manifest describing input/output roots, timeouts, polopt args, and optional case subsets",
    )
    parser.add_argument(
        "--input-dir",
        default="tests/polopt-generated/inputs",
        help="Directory containing .loop inputs",
    )
    parser.add_argument(
        "--output-dir",
        default="tests/polopt-generated/cases",
        help="Directory to populate with one directory per case",
    )
    parser.add_argument(
        "--polopt",
        default="./polopt",
        help="Path to the strict polopt binary",
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=None,
        help="Per-case timeout for invoking polopt (default: 300 unless set by a manifest)",
    )
    parser.add_argument(
        "--polopt-arg",
        action="append",
        default=[],
        help="Extra argument to pass through to polopt; may be repeated",
    )
    parser.add_argument(
        "cases",
        nargs="*",
        help="Optional subset of case stems or filenames to materialize",
    )
    args = parser.parse_args()

    manifest: dict[str, object] = {}
    if args.manifest is not None:
        manifest = load_manifest(pathlib.Path(args.manifest))

    input_dir = pathlib.Path(str(manifest.get("input_dir", args.input_dir)))
    if args.input_dir != parser.get_default("input_dir"):
        input_dir = pathlib.Path(args.input_dir)
    output_dir = pathlib.Path(str(manifest.get("output_dir", args.output_dir)))
    if args.output_dir != parser.get_default("output_dir"):
        output_dir = pathlib.Path(args.output_dir)
    polopt_path = pathlib.Path(str(manifest.get("polopt", args.polopt)))
    if args.polopt != parser.get_default("polopt"):
        polopt_path = pathlib.Path(args.polopt)
    manifest_timeout = manifest.get("timeout_seconds", 300)
    if (
        not isinstance(manifest_timeout, int)
        or isinstance(manifest_timeout, bool)
        or manifest_timeout <= 0
    ):
        raise SystemExit("timeout_seconds must be a positive integer")
    timeout_overridden = args.timeout_seconds is not None
    timeout_seconds = manifest_timeout
    if timeout_overridden:
        timeout_seconds = args.timeout_seconds
    if timeout_seconds is None or timeout_seconds <= 0:
        raise SystemExit("timeout_seconds must be positive")

    case_timeouts = manifest.get("case_timeouts", {})
    if not isinstance(case_timeouts, dict) or not all(
        isinstance(name, str)
        and isinstance(value, int)
        and not isinstance(value, bool)
        and value > 0
        for name, value in case_timeouts.items()
    ):
        raise SystemExit("case_timeouts must map case stems to positive integers")

    polopt_args = manifest.get("polopt_args", [])
    if not isinstance(polopt_args, list) or not all(isinstance(arg, str) for arg in polopt_args):
        raise SystemExit("polopt_args must be a string list")
    if args.polopt_arg:
        polopt_args = list(args.polopt_arg)

    case_specs = manifest.get("cases", [])
    if not isinstance(case_specs, list) or not all(isinstance(case, str) for case in case_specs):
        raise SystemExit("cases must be a string list")
    if args.cases:
        case_specs = list(args.cases)

    root = input_dir.resolve()
    out_root = output_dir.resolve()
    polopt = polopt_path.resolve()

    if not root.is_dir():
        raise SystemExit(f"input dir not found: {root}")
    if not polopt.exists():
        raise SystemExit(f"polopt not found: {polopt}")

    out_root.mkdir(parents=True, exist_ok=True)
    for stale in out_root.iterdir():
        if stale.is_dir() and stale.name.startswith(".") and ".tmp." in stale.name:
            shutil.rmtree(stale)
    if case_specs:
        cases = []
        for case in case_specs:
            name = case if case.endswith(".loop") else f"{case}.loop"
            src = root / name
            if not src.is_file():
                raise SystemExit(f"requested case not found: {src}")
            cases.append(src)
        cases.sort()
    else:
        cases = sorted(root.glob("*.loop"))
    total = len(cases)
    for index, src in enumerate(cases, start=1):
        case_dir = out_root / src.stem
        scratch_dir = pathlib.Path(
            tempfile.mkdtemp(prefix=f".{src.stem}.tmp.", dir=str(out_root))
        )
        print(f"[{index}/{total}] {src.stem}: running", flush=True)
        try:
            case_timeout = (
                timeout_seconds
                if timeout_overridden
                else case_timeouts.get(src.stem, timeout_seconds)
            )
            outcome = run_case(
                polopt,
                list(polopt_args),
                src,
                scratch_dir,
                case_timeout,
            )
            if case_dir.exists():
                shutil.rmtree(case_dir)
            os.replace(scratch_dir, case_dir)
        finally:
            if scratch_dir.exists():
                shutil.rmtree(scratch_dir)
        if outcome["result"] == "ok":
            print(
                f"[{index}/{total}] {src.stem}: ok "
                f"changed={outcome['changed']} "
                f"time={outcome['elapsed_seconds']}s",
                flush=True,
            )
        else:
            print(
                f"[{index}/{total}] {src.stem}: fail "
                f"reason={outcome['reason']} "
                f"time={outcome['elapsed_seconds']}s",
                flush=True,
            )


if __name__ == "__main__":
    main()
