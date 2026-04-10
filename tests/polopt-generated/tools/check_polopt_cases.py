#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys


def load_manifest(path: pathlib.Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"manifest must be a JSON object: {path}")
    return data


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


def strip_outer_if(text: str) -> str:
    stripped = text.strip()
    while stripped.startswith("if "):
        start = stripped.find("{")
        if start < 0:
            break
        depth = 0
        end = None
        for index, ch in enumerate(stripped[start:], start):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = index
                    break
        if end is None or end != len(stripped) - 1:
            break
        stripped = stripped[start + 1:end].strip()
    return stripped + "\n"


def alpha_normalize_loop_vars(text: str) -> str:
    loop_vars: list[str] = []
    for match in re.finditer(r"\bfor\s+([A-Za-z_][A-Za-z0-9_]*)\s+in\s+range\(", text):
        loop_var = match.group(1)
        if loop_var not in loop_vars:
            loop_vars.append(loop_var)
    normalized = text
    for index, loop_var in enumerate(loop_vars):
        normalized = re.sub(
            rf"\b{re.escape(loop_var)}\b",
            f"__iv{index}__",
            normalized,
        )
    return normalized


def is_nontrivially_changed(case_dir: pathlib.Path) -> bool:
    input_text = (case_dir / "input.pretty.loop").read_text()
    opt_text = (case_dir / "optimized.loop").read_text()
    normalized_input = alpha_normalize_loop_vars(strip_outer_if(input_text))
    normalized_opt = alpha_normalize_loop_vars(strip_outer_if(opt_text))
    return normalized_input != normalized_opt


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
        "--manifest",
        default=None,
        help="JSON manifest with suite thresholds and required tiled cases",
    )
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
        "--min-nontrivial-changed",
        type=int,
        default=0,
        help="Minimum number of successful cases that must differ after alpha-normalization and outer-guard stripping",
    )
    parser.add_argument(
        "--require-tiled",
        nargs="*",
        default=[],
        help="Case names that must show explicit tiled bounds in optimized.loop",
    )
    args = parser.parse_args()

    manifest: dict[str, object] = {}
    if args.manifest is not None:
        manifest = load_manifest(pathlib.Path(args.manifest))

    cases_dir = pathlib.Path(str(manifest.get("cases_dir", args.cases_dir)))
    if args.cases_dir != parser.get_default("cases_dir"):
        cases_dir = pathlib.Path(args.cases_dir)
    expect_total = manifest.get("expect_total", args.expect_total)
    if args.expect_total is not None:
        expect_total = args.expect_total
    min_changed = int(manifest.get("min_changed", args.min_changed))
    if args.min_changed != parser.get_default("min_changed"):
        min_changed = args.min_changed
    min_nontrivial_changed = int(
        manifest.get("min_nontrivial_changed", args.min_nontrivial_changed)
    )
    if args.min_nontrivial_changed != parser.get_default("min_nontrivial_changed"):
        min_nontrivial_changed = args.min_nontrivial_changed
    require_tiled_cases = manifest.get("require_tiled", args.require_tiled)
    if args.require_tiled != parser.get_default("require_tiled"):
        require_tiled_cases = args.require_tiled
    if not isinstance(require_tiled_cases, list) or not all(
        isinstance(case, str) for case in require_tiled_cases
    ):
        raise SystemExit("require_tiled must be a list of case names")
    if expect_total is not None:
        expect_total = int(expect_total)

    cases_root = cases_dir
    if not cases_root.is_dir():
        raise SystemExit(f"cases dir not found: {cases_root}")

    case_dirs = sorted(
        p for p in cases_root.iterdir() if p.is_dir() and not p.name.startswith(".")
    )
    total = len(case_dirs)
    ok = 0
    changed = 0
    nontrivial_changed = 0
    failed: list[str] = []
    detected_tiled: list[str] = []

    for case_dir in case_dirs:
        case_ok, case_changed = check_case_dir(case_dir)
        if case_ok:
            ok += 1
            if case_changed:
                changed += 1
                if is_nontrivially_changed(case_dir):
                    nontrivial_changed += 1
            if detect_tiled(case_dir):
                detected_tiled.append(case_dir.name)
        else:
            failed.append(case_dir.name)

    if expect_total is not None and total != expect_total:
        raise SystemExit(f"expected {expect_total} cases, saw {total}")
    if failed:
        raise SystemExit(f"failed cases: {', '.join(failed)}")
    if changed < min_changed:
        raise SystemExit(f"expected at least {min_changed} changed cases, saw {changed}")
    if nontrivial_changed < min_nontrivial_changed:
        raise SystemExit(
            "expected at least "
            f"{min_nontrivial_changed} nontrivially changed cases, "
            f"saw {nontrivial_changed}"
        )

    for case in require_tiled_cases:
        require_tiled(cases_root / case)

    print(f"total={total}")
    print(f"ok={ok}")
    print(f"fail={len(failed)}")
    print(f"changed={changed}")
    print(f"nontrivial_changed={nontrivial_changed}")
    print(f"detected_tiled={len(detected_tiled)}")
    if detected_tiled:
        print(f"detected_tiled_cases={','.join(detected_tiled)}")
    if require_tiled_cases:
        print(f"required_tiled_cases={','.join(require_tiled_cases)}")


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise
