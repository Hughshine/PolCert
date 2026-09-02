#!/usr/bin/env python3

import subprocess
import sys
from pathlib import Path


def run(cmd):
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    return proc.returncode, proc.stdout


def require_contains(label, text, needle):
    if needle not in text:
        raise AssertionError(f"{label}: missing expected text: {needle!r}")


def require_absent(label, text, needle):
    if needle in text:
        raise AssertionError(f"{label}: unexpected text present: {needle!r}")


def main() -> int:
    repo = Path(__file__).resolve().parents[2]
    polopt = repo / "polopt"
    input_loop = repo / "tests" / "polopt-generated" / "inputs" / "matmul.loop"

    if not polopt.exists():
      print(f"[pluto-bug] missing executable: {polopt}", file=sys.stderr)
      return 2

    compat_flags = [
        "--pluto-compat",
        "--tile",
        "--smartfuse",
        "--nointratileopt",
        "--noprevector",
        "--nounrolljam",
        "--rar",
        "--nodiamond-tile",
        "--parallel",
    ]
    debug_cmd = [str(polopt), *compat_flags, str(input_loop)]
    strict_cmd = [str(polopt), *compat_flags, "--parallel-strict", str(input_loop)]

    rc_debug, out_debug = run(debug_cmd)
    if rc_debug != 0:
        print("[pluto-bug] explicit-RAR parallel route failed", file=sys.stderr)
        print(out_debug, end="", file=sys.stderr)
        return rc_debug

    rc_strict, out_strict = run(strict_cmd)
    if rc_strict != 0:
        print("[pluto-bug] correctly mapped strict hint was rejected", file=sys.stderr)
        print(out_strict, end="", file=sys.stderr)
        return rc_strict

    for label, output in (("non-strict run", out_debug), ("strict run", out_strict)):
        require_contains(label, output, "parallel for i1 in range(")
        require_absent(label, output, "parallel for i0 in range(")
        require_absent(label, output, "status=rejected source=pluto-hint")
        require_absent(label, output, "[alarm] requested checked optimization was rejected")

    print("[pluto-bug] explicit-RAR matmul hint certifies the intended loop")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"[pluto-bug] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
