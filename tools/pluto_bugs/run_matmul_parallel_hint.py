#!/usr/bin/env python3

import os
import subprocess
import sys
from pathlib import Path


def run(cmd, env=None):
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=env,
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

    env = os.environ.copy()
    env["POLCERT_DEBUG_PARALLEL_HINT"] = "1"

    debug_cmd = [str(polopt), "--parallel", str(input_loop)]
    strict_cmd = [str(polopt), "--parallel", "--parallel-strict", str(input_loop)]

    rc_debug, out_debug = run(debug_cmd, env=env)
    if rc_debug != 0:
        print("[pluto-bug] polopt --parallel failed", file=sys.stderr)
        print(out_debug, end="", file=sys.stderr)
        return rc_debug

    rc_strict, out_strict = run(strict_cmd, env=env)
    if rc_strict != 0:
        print("[pluto-bug] polopt --parallel --parallel-strict failed", file=sys.stderr)
        print(out_strict, end="", file=sys.stderr)
        return rc_strict

    require_contains("debug run", out_debug, "[debug-parallel] Pluto hint iterator=t1 current_dim=0")
    require_contains("debug run", out_debug, "[debug-parallel] current-dim 0: rejected(")
    require_contains("debug run", out_debug, "[debug-parallel] current-dim 1: accepted(")
    require_contains("debug run", out_debug, "parallel for i1 in range(")
    require_absent("debug run", out_debug, "parallel for i0 in range(")

    require_contains("strict run", out_strict, "[debug-parallel] current-dim 0: rejected(")
    require_contains("strict run", out_strict, "[alarm] optimization triggered a checked fallback or warning")
    require_absent("strict run", out_strict, "parallel for ")

    print("[pluto-bug] matmul parallel-hint case reproduced")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"[pluto-bug] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
