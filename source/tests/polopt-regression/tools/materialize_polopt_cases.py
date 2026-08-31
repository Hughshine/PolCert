#!/usr/bin/env python3
from __future__ import annotations

import argparse
import difflib
import pathlib
import shutil
import subprocess

INPUT_MARKER = "== Input Loop ==\n"
OPT_MARKER = "== Optimized Loop ==\n"


def extract_section(stdout: str, marker: str) -> str:
    start = stdout.find(marker)
    if start < 0:
        raise ValueError(f"missing marker {marker!r}")
    start += len(marker)
    end = stdout.find("\n== ", start)
    if end < 0:
        end = len(stdout)
    return stdout[start:end].strip() + "\n"


def run_case(polopt: pathlib.Path, src: pathlib.Path, out_dir: pathlib.Path, timeout_seconds: int) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, out_dir / "input.loop")

    try:
        proc = subprocess.run(
            [str(polopt), "--dump-input", str(src)],
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        if exc.stderr:
            (out_dir / "stderr.txt").write_text(exc.stderr)
        (out_dir / "status.txt").write_text(
            f"exit_code=timeout\nresult=fail\nreason=timeout({timeout_seconds}s)\n"
        )
        return

    status_lines = [f"exit_code={proc.returncode}"]
    if proc.returncode != 0:
        status_lines.append("result=fail")
        if proc.stderr:
            (out_dir / "stderr.txt").write_text(proc.stderr)
        (out_dir / "status.txt").write_text("\n".join(status_lines) + "\n")
        return

    input_pretty = extract_section(proc.stdout, INPUT_MARKER)
    optimized = extract_section(proc.stdout, OPT_MARKER)
    changed = input_pretty != optimized

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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--input-dir",
        default="tests/polopt-regression/inputs",
        help="Directory containing .loop inputs",
    )
    parser.add_argument(
        "--output-dir",
        default="tests/polopt-regression/cases",
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
        default=120,
        help="Per-case timeout for invoking polopt",
    )
    args = parser.parse_args()

    root = pathlib.Path(args.input_dir)
    out_root = pathlib.Path(args.output_dir)
    polopt = pathlib.Path(args.polopt).resolve()

    if not root.is_dir():
        raise SystemExit(f"input dir not found: {root}")
    if not polopt.exists():
        raise SystemExit(f"polopt not found: {polopt}")

    out_root.mkdir(parents=True, exist_ok=True)
    for src in sorted(root.glob("*.loop")):
        case_dir = out_root / src.stem
        if case_dir.exists():
            shutil.rmtree(case_dir)
        run_case(polopt, src, case_dir, args.timeout_seconds)


if __name__ == "__main__":
    main()
