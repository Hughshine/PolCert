#!/usr/bin/env python3
"""Check that a rejected tiling candidate is observable and not adopted."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess


REJECTED_ROUTE = "[tiling-validation] route=rejected"
FALLBACK_ROUTE = "[tiling-validation] route=general-fallback"
NO_VECTOR_HINT = "[vector-validation] status=skipped reason=no-hint"


def route_lines(stderr: str) -> list[str]:
    return [
        line.strip()
        for line in stderr.splitlines()
        if line.strip().startswith("[tiling-validation] route=")
    ]


def check_rejected_tiling_route(
    *,
    polopt: Path,
    fixture: Path,
    timeout: int,
) -> None:
    wrapper = Path(__file__).resolve().with_name("rejecting_pluto.py")
    real_pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto")).resolve()
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    proc = subprocess.run(
        [str(polopt), "--second-level-tile", str(fixture)],
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env=env,
    )
    if proc.returncode != 0:
        raise AssertionError(
            f"rejected-route probe failed with exit {proc.returncode}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    if route_lines(proc.stderr) != [REJECTED_ROUTE]:
        raise AssertionError(
            "rejected tiling did not report exactly one rejected route\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    if "[rejecting-pluto] corrupted one second-level tile-link" not in proc.stderr:
        raise AssertionError("the rejection probe did not mutate the tiling output")
    if "[alarm]" in proc.stderr:
        raise AssertionError("retaining the validated affine midpoint raised an alarm")
    if "== Optimized Loop ==" not in proc.stdout:
        raise AssertionError("rejected tiling did not return the affine midpoint output")
    for marker in ("/ 256", "8 *", "32 *"):
        if marker in proc.stdout:
            raise AssertionError(
                f"rejected second-level tiling leaked nested tile marker {marker!r}"
            )

    root = Path(__file__).resolve().parents[2]
    scalar_only = subprocess.run(
        [
            str(polopt),
            "--second-level-tile",
            str(root / "tests" / "polopt-regression" / "inputs" / "noloop.loop"),
        ],
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env=os.environ.copy(),
    )
    if scalar_only.returncode != 0:
        raise AssertionError("scalar-only rejected-route probe failed")
    if route_lines(scalar_only.stderr) != [REJECTED_ROUTE]:
        raise AssertionError(
            "a tiling request with no non-scalar statement was not explicitly rejected"
        )
    if "[alarm]" in scalar_only.stderr or "s = 0;" not in scalar_only.stdout:
        raise AssertionError("scalar-only rejection did not preserve the original program")

    strict_fixture = root / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
    for second_level in (False, True):
        for use_iss in (False, True):
            args = ["--identity", "--tile"]
            if second_level:
                args.append("--second-level-tile")
            if use_iss:
                args.append("--iss")
            args.extend(
                (
                    "--vector",
                    "--vector-strict",
                    "--nointratileopt",
                    "--nounrolljam",
                    "--nodiamond-tile",
                    "--noparallel",
                    str(strict_fixture),
                )
            )
            strict = subprocess.run(
                [str(polopt), *args],
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
                env=os.environ.copy(),
            )
            label = (
                f"{'second-level ' if second_level else ''}"
                f"identity vector-strict{' ISS' if use_iss else ''}"
            )
            if strict.returncode != 0:
                raise AssertionError(f"{label} conservative fallback failed")
            if route_lines(strict.stderr) != [FALLBACK_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve its verified fallback route"
                )
            if "[alarm]" in strict.stderr:
                raise AssertionError(f"{label} raised an alarm for an optional annotation")
            if NO_VECTOR_HINT not in strict.stderr:
                raise AssertionError(f"{label} omitted its no-hint vector telemetry")
            if "vector for" in strict.stdout:
                raise AssertionError(f"{label} adopted a rejected vector consumer")
            expected_markers = ("/ 256", "8 *", "32 *") if second_level else ("/ 32", "32 *")
            for marker in expected_markers:
                if marker not in strict.stdout:
                    raise AssertionError(
                        f"{label} lost verified tiling marker {marker!r}"
                    )

    for second_level in (False, True):
        for use_iss in (False, True):
            for current_flag in ("--parallel-current", "--vector-current"):
                args = []
                if second_level:
                    args.append("--second-level-tile")
                if use_iss:
                    args.append("--iss")
                args.extend((current_flag, "999", str(strict_fixture)))
                current = subprocess.run(
                    [str(polopt), *args],
                    text=True,
                    capture_output=True,
                    timeout=timeout,
                    check=False,
                    env=os.environ.copy(),
                )
                label = (
                    f"{'second-level ' if second_level else 'ordinary '}"
                    f"{current_flag[2:]}{' ISS' if use_iss else ''}"
                )
                if current.returncode == 0:
                    raise AssertionError(f"{label} invalid dimension unexpectedly succeeded")
                expected_routes = [] if current_flag == "--vector-current" else [REJECTED_ROUTE]
                if route_lines(current.stderr) != expected_routes:
                    raise AssertionError(
                        f"{label} hard failure reported unexpected tiling routes"
                    )
                if current_flag == "--vector-current":
                    rejection = (
                        "[vector-validation] status=rejected source=explicit-current "
                        "reason=not-certifiable-or-non-innermost"
                    )
                    if current.stderr.count(rejection) != 1:
                        raise AssertionError(
                            f"{label} omitted its unique vector rejection telemetry"
                        )
                if "validation failed" not in current.stderr.lower():
                    raise AssertionError(f"{label} omitted its validation failure")

    print(
        "rejected tiling route: PASS "
        "(invalid witness, scalar-only early exit, four vector skips preserve "
        "their verified fallbacks, and eight explicit-current failures are explicit)"
    )


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    check_rejected_tiling_route(
        polopt=(root / "polopt").resolve(),
        fixture=(
            root
            / "tools"
            / "second_level_tiling"
            / "fixtures"
            / "symbolic-independent-2d.loop"
        ),
        timeout=180,
    )
