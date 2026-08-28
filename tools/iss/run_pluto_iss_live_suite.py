#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
PLUTO = Path("/pluto/tool/pluto")
ISS_TOOL = ROOT / "tools" / "iss" / "pluto_iss_check.py"
VALIDATION_REJECTION = "validation: FAIL"


def is_validation_rejection(code: int, output: str) -> bool:
    return code == 1 and VALIDATION_REJECTION in output


def run_bridge_checker(bridge: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [str(POLOPT), "--validate-iss-bridge", str(bridge)],
        capture_output=True,
        text=True,
    )
    output = proc.stdout.strip()
    if proc.stderr.strip():
        output = (output + "\n" + proc.stderr.strip()).strip()
    return proc.returncode, output


def emit_pluto_bridge(src: Path, dst: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [
            str(PLUTO),
            "--pet",
            "--iss",
            "--identity",
            "--moredebug",
            "--silent",
            str(src),
        ],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        output = proc.stdout.strip()
        if proc.stderr.strip():
            output = (output + "\n" + proc.stderr.strip()).strip()
        return proc.returncode, output

    with tempfile.TemporaryDirectory(prefix="iss-live-emit-") as tmpdir:
        combined = Path(tmpdir) / f"{src.stem}.combined.txt"
        combined.write_text(proc.stdout)
        bridge_proc = subprocess.run(
            [
                sys.executable,
                str(ISS_TOOL),
                "--emit-bridge-from-combined",
                str(combined),
            ],
            capture_output=True,
            text=True,
        )

    dst.write_text(bridge_proc.stdout)
    output = bridge_proc.stdout.strip()
    if bridge_proc.stderr.strip():
        output = (output + "\n" + bridge_proc.stderr.strip()).strip()
    return bridge_proc.returncode, output


def mutate_bad_cut(src: Path, dst: Path) -> None:
    text = src.read_text()
    for line in text.splitlines():
        if line.startswith("CUT "):
            payload = line[len("CUT ") :]
            coeffs, const = payload.split("|", 1)
            bad = f"CUT {coeffs}|{int(const) + 1}"
            dst.write_text(text.replace(line, bad, 1))
            return
    raise ValueError("bridge did not contain any CUT row to corrupt")


def main() -> int:
    positives = [
        Path("/pluto/test/jacobi-2d-periodic.c"),
        Path("/pluto/test/multi-stmt-periodic.c"),
        Path("/pluto/test/heat-2dp.c"),
    ]
    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="iss-live-suite-") as tmpdir:
        tmp = Path(tmpdir)
        emitted: list[Path] = []

        for src in positives:
            bridge = tmp / f"{src.stem}.bridge.txt"
            code, output = emit_pluto_bridge(src, bridge)
            emitted_ok = code == 0 and "VAR_ORDER" in bridge.read_text()
            print(
                f"[ISS-LIVE] {'PASS' if emitted_ok else 'FAIL'} case={src.name}-emit "
                f"expected=bridge-with-var-order actual={'bridge-emitted' if emitted_ok else 'emit-failure'},exit:{code} "
                "interpretation="
                + (
                    "Pluto-live-ISS-bridge-was-emitted"
                    if emitted_ok
                    else "Pluto-live-ISS-bridge-emission-failed"
                )
            )
            if not emitted_ok:
                failures.append(f"bridge emission failed: {src.name}\n{output}")
                continue
            emitted.append(bridge)
            code, output = run_bridge_checker(bridge)
            print(
                f"[ISS-LIVE] {'PASS' if code == 0 else 'FAIL'} case={src.name}-validate "
                f"expected=accept actual={'accept' if code == 0 else 'reject'},exit:{code} "
                "interpretation="
                + (
                    "live-Pluto-ISS-witness-was-accepted"
                    if code == 0
                    else "live-Pluto-ISS-witness-was-unexpectedly-rejected"
                )
            )
            if code != 0:
                failures.append(f"live positive case failed: {src.name}\n{output}")

        if emitted:
            bad_bridge = tmp / "bad_cut.bridge.txt"
            mutate_bad_cut(emitted[0], bad_bridge)
            code, output = run_bridge_checker(bad_bridge)
            rejected = is_validation_rejection(code, output)
            print(
                f"[ISS-LIVE] {'PASS' if rejected else 'FAIL'} case=mutated-cut "
                "expected=reject,exit:1,validation-fail:true "
                f"actual=exit:{code},validation-fail:{str(VALIDATION_REJECTION in output).lower()} "
                "interpretation="
                + (
                    "mutated-live-ISS-witness-was-rejected"
                    if rejected
                    else "mutated-live-ISS-witness-did-not-produce-the-declared-rejection"
                )
            )
            if not rejected:
                failures.append("live negative bridge was not cleanly rejected\n" + output)

    if failures:
        print("[ISS-LIVE-SUITE] FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        "[ISS-LIVE-SUITE] PASS expected=emitted:3,accepted:3,rejected:1 "
        "actual=emitted:3,accepted:3,rejected:1 interpretation=live-ISS-contracts-matched"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
