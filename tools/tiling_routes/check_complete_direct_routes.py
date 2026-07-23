#!/usr/bin/env python3
"""Check representative cases through the complete direct-only tiling route."""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNTIME_ROUTE_RE = re.compile(
    r"^\[tiling-validation\] route=(permutable-band|rejected)$",
    re.MULTILINE,
)
PAIR_ROUTE_RE = re.compile(r"\(route=(permutable-band|rejected)\)")


def run_case(
    executable: pathlib.Path,
    args: list[str],
    expected_route: str,
    timeout: int,
) -> str | None:
    env = os.environ.copy()
    env.setdefault("COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini"))
    with tempfile.TemporaryDirectory(prefix="polcert-direct-band-") as tmp:
        try:
            proc = subprocess.run(
                [str(executable), *args],
                cwd=tmp,
                env=env,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return f"timed out after {timeout}s: {' '.join(args)}"

    output = proc.stdout + proc.stderr
    if expected_route == "rejected":
        if proc.returncode == 0:
            return f"rejected route exited successfully: {' '.join(args)}\n{output}"
    elif proc.returncode != 0:
        return f"exit {proc.returncode}: {' '.join(args)}\n{output}"
    matches = RUNTIME_ROUTE_RE.findall(output)
    if not matches:
        matches = PAIR_ROUTE_RE.findall(output)
    if len(matches) != 1:
        return f"expected one production route, found {len(matches)}\n{output}"
    if matches[0] != expected_route:
        return (
            f"expected route={expected_route}, got route={matches[0]}: "
            f"{' '.join(args)}"
        )
    if "fallback" in output:
        return f"fallback marker in direct-only route output: {' '.join(args)}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polopt", default="./polopt")
    parser.add_argument("--polcert", default="./polcert")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    polopt = pathlib.Path(args.polopt).resolve()
    polcert = pathlib.Path(args.polcert).resolve()
    if not polopt.is_file():
        raise SystemExit(f"missing polopt: {polopt}")
    if not polcert.is_file():
        raise SystemExit(f"missing polcert: {polcert}")

    cases = [
        (
            "ordinary-common-band",
            polopt,
            [str(ROOT / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop")],
            "permutable-band",
        ),
        (
            "ordinary-phase-separated-mixed-depth",
            polopt,
            [
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
        ),
        (
            "ordinary-phase-separated-mixed-depth-iss",
            polopt,
            [
                "--iss",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
        ),
        (
            "mixed-depth-semantic-band",
            polopt,
            [
                "--identity-tiled",
                str(
                    ROOT
                    / "tools"
                    / "second_level_tiling"
                    / "fixtures"
                    / "matmul-init.loop"
                ),
            ],
            "permutable-band",
        ),
        (
            "dependent-one-dimensional-band",
            polopt,
            [str(ROOT / "tools" / "parallel_current" / "fixtures" / "dependent.loop")],
            "permutable-band",
        ),
        (
            "frozen-diamond-phase-pair",
            polcert,
            [
                "--tiling",
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "diamond-tile-example.midtransform.scop"),
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "diamond-tile-example.posttile.scop"),
            ],
            "permutable-band",
        ),
        (
            "frozen-nonpermutable-band",
            polcert,
            [
                "--tiling",
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "nonpermutable-band.midtransform.scop"),
                str(ROOT / "tools" / "tiling_routes" / "fixtures" / "nonpermutable-band.posttile.scop"),
            ],
            "rejected",
        ),
    ]

    failures: list[str] = []
    for name, executable, command_args, expected_route in cases:
        failure = run_case(executable, command_args, expected_route, args.timeout)
        print(f"[direct-route] {name}: {'PASS' if failure is None else 'FAIL'}")
        if failure is not None:
            failures.append(f"{name}: {failure}")
    if failures:
        print("[direct-route] FAIL")
        print("\n".join(failures))
        return 1
    print(f"[direct-route] OK ({len(cases)} cases, zero fallbacks)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
