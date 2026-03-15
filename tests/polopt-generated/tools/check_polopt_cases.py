#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys


def parse_status(path: pathlib.Path) -> dict[str, str]:
    data: dict[str, str] = {}
    for line in path.read_text().splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        data[key.strip()] = value.strip()
    return data


def check_case_dir(case_dir: pathlib.Path) -> tuple[bool, bool]:
    status_path = case_dir / "status.txt"
    if not status_path.exists():
        raise SystemExit(f"missing status.txt for case {case_dir.name}")
    status = parse_status(status_path)
    result = status.get("result")
    if result != "ok":
        return False, False
    changed = status.get("changed") == "true"
    return True, changed


def loop_count(text: str) -> int:
    return text.count("for ")


def detect_tiled(case_dir: pathlib.Path) -> bool:
    input_path = case_dir / "input.pretty.loop"
    opt_path = case_dir / "optimized.loop"
    if not input_path.exists() or not opt_path.exists():
        raise SystemExit(f"missing loop dump(s) for case {case_dir.name}")
    input_text = input_path.read_text()
    opt_text = opt_path.read_text()
    return (
        loop_count(opt_text) >= loop_count(input_text) + 2
        and "max(" in opt_text
        and "min(" in opt_text
        and ("/ 32" in opt_text or "/32" in opt_text)
    )


def require_tiled(case_dir: pathlib.Path) -> None:
    opt_path = case_dir / "optimized.loop"
    if not opt_path.exists():
        raise SystemExit(f"missing optimized.loop for tiled case {case_dir.name}")
    if not detect_tiled(case_dir):
        input_text = (case_dir / "input.pretty.loop").read_text()
        opt_text = opt_path.read_text()
        raise SystemExit(
            "case "
            f"{case_dir.name} is not detected as tiled "
            f"(input_loops={loop_count(input_text)}, optimized_loops={loop_count(opt_text)})"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cases-dir",
        default="tests/polopt-generated/cases",
        help="Directory containing materialized per-case outputs",
    )
    parser.add_argument(
        "--expect-total",
        type=int,
        default=None,
        help="Expected number of cases",
    )
    parser.add_argument(
        "--min-changed",
        type=int,
        default=0,
        help="Minimum number of successful cases that must differ from input",
    )
    parser.add_argument(
        "--require-tiled",
        nargs="*",
        default=[],
        help="Case names that must show explicit tiled bounds in optimized.loop",
    )
    args = parser.parse_args()

    cases_root = pathlib.Path(args.cases_dir)
    if not cases_root.is_dir():
        raise SystemExit(f"cases dir not found: {cases_root}")

    case_dirs = sorted(p for p in cases_root.iterdir() if p.is_dir())
    total = len(case_dirs)
    ok = 0
    changed = 0
    failed: list[str] = []
    detected_tiled: list[str] = []

    for case_dir in case_dirs:
        case_ok, case_changed = check_case_dir(case_dir)
        if case_ok:
            ok += 1
            if case_changed:
                changed += 1
            if detect_tiled(case_dir):
                detected_tiled.append(case_dir.name)
        else:
            failed.append(case_dir.name)

    if args.expect_total is not None and total != args.expect_total:
        raise SystemExit(f"expected {args.expect_total} cases, saw {total}")
    if failed:
        raise SystemExit(f"failed cases: {', '.join(failed)}")
    if changed < args.min_changed:
        raise SystemExit(f"expected at least {args.min_changed} changed cases, saw {changed}")

    for case in args.require_tiled:
        require_tiled(cases_root / case)

    print(f"total={total}")
    print(f"ok={ok}")
    print(f"fail={len(failed)}")
    print(f"changed={changed}")
    print(f"detected_tiled={len(detected_tiled)}")
    if detected_tiled:
        print(f"detected_tiled_cases={','.join(detected_tiled)}")
    if args.require_tiled:
        print(f"required_tiled_cases={','.join(args.require_tiled)}")


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise
