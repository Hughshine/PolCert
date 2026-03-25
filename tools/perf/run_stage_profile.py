#!/usr/bin/env python3

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List


PROFILE_RE = re.compile(r"^\[profile\]\s+([A-Za-z0-9_.-]+)\s+(.+)$")


def mode_args(mode: str) -> List[str]:
    if mode == "identity":
        return ["--identity"]
    if mode == "affine":
        return ["--notile"]
    if mode == "full":
        return []
    if mode == "iss-affine":
        return ["--iss", "--notile"]
    raise ValueError(f"unsupported mode: {mode}")


def parse_profile(stderr: str) -> Dict[str, str]:
    data: Dict[str, str] = {}
    for line in stderr.splitlines():
        match = PROFILE_RE.match(line.strip())
        if not match:
            continue
        data[match.group(1)] = match.group(2)
    return data


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run polopt --profile-stages on a loop case and summarize output."
    )
    parser.add_argument("--polopt", default="./polopt")
    parser.add_argument(
        "--mode",
        choices=["identity", "affine", "full", "iss-affine"],
        default="affine",
    )
    parser.add_argument("--timeout-seconds", type=int, default=300)
    parser.add_argument("--json-out")
    parser.add_argument("loop_input")
    args = parser.parse_args()

    loop_input = Path(args.loop_input)
    if not loop_input.is_file():
        print(f"[perf] missing loop input: {loop_input}", file=sys.stderr)
        return 2

    cmd = [args.polopt, "--profile-stages", *mode_args(args.mode), str(loop_input)]
    proc = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=args.timeout_seconds,
        check=False,
    )

    sys.stdout.write(proc.stdout)
    profile = parse_profile(proc.stderr)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        print(
            f"[perf] polopt exited with {proc.returncode} for mode={args.mode}",
            file=sys.stderr,
        )
        return proc.returncode

    if not profile:
        sys.stderr.write(proc.stderr)
        print("[perf] no [profile] output found", file=sys.stderr)
        return 1

    print(f"[perf] mode={args.mode}")
    for key in [
        "extract",
        "strengthen",
        "affine_schedule",
        "normalize_codegen",
        "prepare_codegen",
        "codegen_elim_schedule",
        "codegen_ast_generate",
        "codegen_polyloop_simpl",
        "codegen_loopgen",
        "cleanup",
        "total",
        "codegen_input.pis",
        "codegen_input.domain_rows",
        "polyloop_raw.nodes",
        "polyloop_raw.loops",
        "polyloop_raw.guards",
        "polyloop_raw.instrs",
        "polyloop_raw.constraints",
        "polyloop_simpl.constraints",
    ]:
        if key in profile:
            print(f"[perf]   {key} = {profile[key]}")

    if args.json_out:
        payload = {
            "mode": args.mode,
            "loop_input": str(loop_input),
            "command": cmd,
            "profile": profile,
        }
        Path(args.json_out).write_text(json.dumps(payload, indent=2, sort_keys=True))
        print(f"[perf] wrote {args.json_out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
