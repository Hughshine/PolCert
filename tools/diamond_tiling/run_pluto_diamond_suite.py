#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
POLCERT = ROOT / "polcert"
PLUTO = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
PLUTO_TEST_DIR = Path(os.environ.get("PLUTO_TEST_DIR", "/pluto/test"))

COMMON_PLUTO_FLAGS = [
    "--silent",
    "--dumpscop",
    "--tile",
    "--noparallel",
    "--nointratileopt",
    "--nounrolljam",
    "--noprevector",
]

SUPPORTED_CASES: dict[str, dict[str, object]] = {
    "diamond-tile-example.c": {"kind": "diamond", "phase_ok": True},
    "fdtd-2d.c": {"kind": "diamond", "phase_ok": True},
    "heat-3d-imperfect.c": {"kind": "diamond", "phase_ok": True},
    "jacobi-1d-imper.c": {"kind": "diamond", "phase_ok": True},
    "jacobi-2d-imper.c": {"kind": "diamond", "phase_ok": True},
    "jacobi-2d.c": {"kind": "diamond", "phase_ok": True},
    "multi-stmt-stencil-seq.c": {"kind": "no_effect", "phase_ok": True},
    "seidel.c": {"kind": "no_effect", "phase_ok": True},
}

UNSUPPORTED_CASES = [
    "heat-2d.c",
    "heat-2dp.c",
    "heat-3d.c",
    "jacobi-1d-mod.c",
    "jacobi-1d-periodic-even.c",
    "jacobi-1d-periodic.c",
    "jacobi-2d-17pt.c",
    "jacobi-2d-imper.par2d.c",
    "jacobi-2d-periodic.c",
    "jacobi-3d-25pt.c",
    "jacobi-3d-periodic.c",
]


def run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd is not None else None,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def require_file(path: Path) -> None:
    if not path.exists():
        raise AssertionError(f"missing expected file: {path}")


def witness_has_mixed_affine(text: str) -> bool:
    for line in text.splitlines():
        if "tile link:" not in line or "floor(" not in line or "/" not in line:
            continue
        expr = line.split("floor(", 1)[1].split("/", 1)[0]
        if "+" in expr or "-" in expr[1:]:
            return True
    return False


def phase_validation_succeeds(text: str) -> bool:
    return (
        "[PHASE] affine(before, mid): OK" in text
        and "[PHASE] tiling(mid, posttile): OK" in text
        and "[PHASE] affine(posttile, after): OK" in text
        and "[OK] Diamond phase-aligned validation succeeded" in text
    )


def first_nonempty_line(text: str) -> str:
    for line in text.splitlines():
        stripped = line.strip()
        if stripped:
            return stripped
    return ""


def classify_pluto_rejection(result: dict[str, object]) -> tuple[str, str]:
    if result["timed_out"]:
        return ("timeout", "Pluto timed out")
    stderr = str(result["stderr"])
    stdout = str(result["stdout"])
    combined = stderr + "\n" + stdout
    if "[Clan] Error:" in combined or "Error extracting polyhedra" in combined:
        reason = first_nonempty_line(stderr) or "Error extracting polyhedra from source file"
        return ("pluto_frontend_rejected", reason)
    if result["returncode"] != 0:
        reason = first_nonempty_line(stderr) or first_nonempty_line(stdout)
        return ("pluto_rejected", reason or f"Pluto exited with {result['returncode']}")
    return ("unexpected_success", "")


def run_pluto_case(
    case_name: str,
    case_root: Path,
    *,
    diamond: bool,
    timeout: int,
) -> dict[str, object]:
    mode = "diamond" if diamond else "nodiamond"
    run_root = case_root / mode
    run_root.mkdir(parents=True, exist_ok=True)
    src = PLUTO_TEST_DIR / case_name
    shutil.copy2(src, run_root / case_name)

    extra_flag = "--diamond-tile" if diamond else "--nodiamond-tile"
    cmd = [str(PLUTO), *COMMON_PLUTO_FLAGS, extra_flag, case_name]
    try:
        proc = run(cmd, cwd=run_root, timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired as exc:
        proc = subprocess.CompletedProcess(
            cmd,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )
        timed_out = True

    write_text(run_root / "pluto.stdout.txt", proc.stdout)
    write_text(run_root / "pluto.stderr.txt", proc.stderr)

    stem = Path(case_name).stem
    before = run_root / f"{stem}.beforescheduling.scop"
    mid = run_root / f"{stem}.midtransform.scop"
    posttile = run_root / f"{stem}.posttile.scop"
    after = run_root / f"{stem}.afterscheduling.scop"

    return {
        "cmd": cmd,
        "returncode": proc.returncode,
        "timed_out": timed_out,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "before": before,
        "mid": mid,
        "posttile": posttile,
        "after": after,
        "root": run_root,
    }


def run_polopt(label: str, args: list[str], case_root: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    cmd = [str(POLOPT), *args]
    try:
        proc = run(cmd, cwd=ROOT, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        proc = subprocess.CompletedProcess(
            cmd,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )
    write_text(case_root / f"{label}.stdout.txt", proc.stdout)
    write_text(case_root / f"{label}.stderr.txt", proc.stderr)
    return proc


def run_polcert_phase(before: Path, mid: Path, posttile: Path, after: Path, case_root: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    cmd = [str(POLCERT), str(before), str(mid), str(posttile), str(after)]
    try:
        proc = run(
            cmd,
            cwd=ROOT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        proc = subprocess.CompletedProcess(
            cmd,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )
    write_text(case_root / "phase.stdout.txt", proc.stdout)
    write_text(case_root / "phase.stderr.txt", proc.stderr)
    return proc


def check_supported_case(case_name: str, expectation: dict[str, object], out_root: Path, timeout: int) -> tuple[dict[str, object], list[str]]:
    case_root = out_root / Path(case_name).stem
    failures: list[str] = []

    nodiamond = run_pluto_case(case_name, case_root, diamond=False, timeout=timeout)
    diamond = run_pluto_case(case_name, case_root, diamond=True, timeout=timeout)

    if nodiamond["returncode"] != 0:
        failures.append(f"{case_name}: nodiamond Pluto failed with exit={nodiamond['returncode']}")
        return ({"case": case_name, "status": "error"}, failures)
    if diamond["returncode"] != 0:
        failures.append(f"{case_name}: diamond Pluto failed with exit={diamond['returncode']}")
        return ({"case": case_name, "status": "error"}, failures)

    for key in ["before", "mid", "posttile", "after"]:
        require_file(diamond[key])  # type: ignore[index]
    require_file(nodiamond["mid"])  # type: ignore[arg-type]

    midpoint_changed = (
        Path(nodiamond["mid"]).read_bytes() != Path(diamond["mid"]).read_bytes()
    )
    observed_kind = "diamond" if midpoint_changed else "no_effect"
    expected_kind = str(expectation["kind"])
    if observed_kind != expected_kind:
        failures.append(
            f"{case_name}: expected {expected_kind}, observed {observed_kind}"
        )

    affine = run_polopt(
        "affine",
        [
            "--validate-affine-openscop",
            str(diamond["before"]),
            str(diamond["mid"]),
        ],
        case_root,
        timeout,
    )
    if affine.returncode == 124:
        failures.append(f"{case_name}: affine validator timed out")
    elif affine.returncode != 0 or "overall: PASS" not in affine.stdout:
        failures.append(f"{case_name}: affine validator failed")

    tiling = run_polopt(
        "tiling",
        [
            "--validate-tiling-openscop",
            str(diamond["mid"]),
            str(diamond["posttile"]),
        ],
        case_root,
        timeout,
    )
    if tiling.returncode == 124:
        failures.append(f"{case_name}: OpenScop tiling validator timed out")
    elif tiling.returncode != 0 or "overall: PASS" not in tiling.stdout:
        failures.append(f"{case_name}: OpenScop tiling validator failed")

    witness = run_polopt(
        "witness",
        [
            "--extract-tiling-witness-openscop",
            str(diamond["mid"]),
            str(diamond["posttile"]),
        ],
        case_root,
        timeout,
    )
    mixed_affine = witness_has_mixed_affine(witness.stdout)
    if witness.returncode == 124:
        failures.append(f"{case_name}: witness extraction timed out")
    elif witness.returncode != 0:
        failures.append(f"{case_name}: witness extraction failed")
    elif expected_kind == "diamond" and not mixed_affine:
        failures.append(f"{case_name}: witness did not expose a mixed affine diamond link")

    phase = run_polcert_phase(
        Path(diamond["before"]),
        Path(diamond["mid"]),
        Path(diamond["posttile"]),
        Path(diamond["after"]),
        case_root,
        timeout,
    )
    phase_ok = phase_validation_succeeds(phase.stdout)
    if phase.returncode == 124:
        failures.append(f"{case_name}: phase validator timed out")
    elif phase_ok != bool(expectation["phase_ok"]):
        failures.append(
            f"{case_name}: expected phase_ok={expectation['phase_ok']}, observed {phase_ok}"
        )

    result = {
        "case": case_name,
        "status": observed_kind,
        "midpoint_changed": midpoint_changed,
        "affine_ok": affine.returncode == 0 and "overall: PASS" in affine.stdout,
        "tiling_ok": tiling.returncode == 0 and "overall: PASS" in tiling.stdout,
        "witness_mixed_affine": mixed_affine,
        "phase_ok": phase_ok,
    }
    return (result, failures)


def check_unsupported_case(case_name: str, out_root: Path, timeout: int) -> tuple[dict[str, object], list[str]]:
    case_root = out_root / Path(case_name).stem
    failures: list[str] = []
    diamond = run_pluto_case(case_name, case_root, diamond=True, timeout=timeout)
    status, reason = classify_pluto_rejection(diamond)
    if diamond["returncode"] == 0:
        failures.append(f"{case_name}: expected unsupported Pluto input, but command succeeded")
    result = {
        "case": case_name,
        "status": status,
        "reason": reason,
        "returncode": diamond["returncode"],
        "timed_out": diamond["timed_out"],
    }
    return (result, failures)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout-seconds", type=int, default=180)
    ap.add_argument("--keep-artifacts", action="store_true")
    ap.add_argument("--output-root")
    args = ap.parse_args()

    if not POLOPT.exists():
        print(f"[diamond-suite] missing executable: {POLOPT}", file=sys.stderr)
        return 2
    if not POLCERT.exists():
        print(f"[diamond-suite] missing executable: {POLCERT}", file=sys.stderr)
        return 2
    if not PLUTO.exists():
        print(f"[diamond-suite] missing Pluto binary: {PLUTO}", file=sys.stderr)
        return 2
    if not PLUTO_TEST_DIR.exists():
        print(f"[diamond-suite] missing Pluto test directory: {PLUTO_TEST_DIR}", file=sys.stderr)
        return 2

    if args.output_root:
        out_root = Path(args.output_root).resolve()
        if out_root.exists():
            shutil.rmtree(out_root)
        out_root.mkdir(parents=True, exist_ok=True)
        cleanup_root = False
    else:
        out_root = Path(tempfile.mkdtemp(prefix="polcert-diamond-suite-"))
        cleanup_root = not args.keep_artifacts

    failures: list[str] = []
    results: list[dict[str, object]] = []

    try:
        for case_name, expectation in SUPPORTED_CASES.items():
            result, case_failures = check_supported_case(
                case_name,
                expectation,
                out_root,
                args.timeout_seconds,
            )
            results.append(result)
            failures.extend(case_failures)
            print(
                f"[diamond-suite] {case_name}: status={result['status']} "
                f"affine={result.get('affine_ok')} tiling={result.get('tiling_ok')} "
                f"phase={result.get('phase_ok')}"
            )

        for case_name in UNSUPPORTED_CASES:
            result, case_failures = check_unsupported_case(
                case_name,
                out_root,
                args.timeout_seconds,
            )
            results.append(result)
            failures.extend(case_failures)
            print(
                f"[diamond-suite] {case_name}: status={result['status']} "
                f"exit={result.get('returncode')} reason={result.get('reason')}"
            )

        summary = {
            "pluto": str(PLUTO),
            "pluto_test_dir": str(PLUTO_TEST_DIR),
            "results": results,
            "failures": failures,
        }
        write_text(out_root / "summary.json", json.dumps(summary, indent=2, sort_keys=True))

        if failures:
            print("[diamond-suite] FAIL")
            for failure in failures:
                print(f"  - {failure}")
            print(f"[diamond-suite] artifacts: {out_root}")
            cleanup_root = False
            return 1

        print("[diamond-suite] OK")
        print(f"[diamond-suite] artifacts: {out_root}")
        return 0
    finally:
        if cleanup_root:
            shutil.rmtree(out_root, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
