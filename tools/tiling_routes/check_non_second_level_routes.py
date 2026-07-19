#!/usr/bin/env python3
"""Require specialized validation for every supported one-level tiling route."""

from __future__ import annotations

import argparse
import os
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
ROUTE_PREFIX = "[tiling-validation] route="
PERMUTABLE_ROUTE = f"{ROUTE_PREFIX}permutable-band"
GENERAL_FALLBACK_ROUTE = f"{ROUTE_PREFIX}general-fallback"
VECTOR_PREFIX = "[vector-validation] "


@dataclass(frozen=True)
class Case:
    name: str
    fixture: Path
    args: tuple[str, ...]
    expected_route: str = "permutable-band"
    expect_alarm: bool = False
    expect_success: bool = True
    expected_vector_status: str | None = None


SYMBOLIC = (
    ROOT / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop"
)
MATMUL_INIT = (
    ROOT / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
)
DIAMOND = (
    ROOT / "tools" / "parallel_current" / "fixtures" / "diamond-example-inner-batch.loop"
)

CONSUMERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("sequential", ()),
    ("parallel-hint", ("--parallel",)),
    ("parallel-strict", ("--parallel", "--parallel-strict")),
    (
        "multipar",
        (
            "--parallel",
            "--multipar",
            "--nointratileopt",
            "--noprevector",
            "--nounrolljam",
        ),
    ),
    (
        "multipar-strict",
        (
            "--parallel",
            "--multipar",
            "--parallel-strict",
            "--nointratileopt",
            "--noprevector",
            "--nounrolljam",
        ),
    ),
    ("vector-hint", ("--vector",)),
    ("vector-strict", ("--vector", "--vector-strict")),
    ("parallel-current", ("--parallel-current", "1")),
    ("vector-current", ("--vector-current", "1")),
)

PRODUCERS: tuple[tuple[str, tuple[str, ...], Path], ...] = (
    ("ordinary", (), SYMBOLIC),
    ("identity", ("--identity-tiled",), SYMBOLIC),
    ("diamond", ("--diamond-tile",), DIAMOND),
    ("full-diamond", ("--full-diamond-tile",), DIAMOND),
)


def route_cases() -> list[Case]:
    cases: list[Case] = []
    for producer_name, producer_args, fixture in PRODUCERS:
        for iss_name, iss_args in (("", ()), ("-iss", ("--iss",))):
            for consumer_name, consumer_args in CONSUMERS:
                effective_consumer_args = consumer_args
                if producer_name in ("ordinary", "identity") and "--multipar" in consumer_args:
                    effective_consumer_args = (*consumer_args, "--nodiamond-tile")
                if producer_name in ("diamond", "full-diamond") and consumer_name.endswith("-current"):
                    effective_consumer_args = (*consumer_args[:-1], "0")
                elif consumer_name == "vector-current":
                    effective_consumer_args = (*consumer_args[:-1], "3")
                vector_current_rejected = (
                    producer_name in ("diamond", "full-diamond")
                    and consumer_name == "vector-current"
                )
                if consumer_name in ("vector-hint", "vector-strict"):
                    vector_status = (
                        "status=skipped reason=hint-not-certifiable-or-non-innermost"
                        if producer_name in ("diamond", "full-diamond")
                        else "status=applied source=pluto-hint scope=innermost"
                    )
                elif consumer_name == "vector-current":
                    vector_status = (
                        "status=rejected source=explicit-current "
                        "reason=not-certifiable-or-non-innermost"
                        if vector_current_rejected
                        else "status=applied source=explicit-current scope=innermost"
                    )
                else:
                    vector_status = None
                cases.append(
                    Case(
                        name=f"{producer_name}{iss_name}-{consumer_name}",
                        fixture=fixture,
                        args=(*producer_args, *iss_args, *effective_consumer_args),
                        expected_route=(
                            "rejected" if vector_current_rejected else "permutable-band"
                        ),
                        expect_success=not vector_current_rejected,
                        expected_vector_status=vector_status,
                    )
                )

    # Static scattering rows are compressed on this mixed-depth input. These
    # cases lock the whole-program ordinary-tiling mode that covers that shape.
    for iss_name, iss_args in (("", ()), ("-iss", ("--iss",))):
        for consumer_name, consumer_args in (
            ("sequential", ()),
            ("parallel-hint", ("--parallel",)),
            ("parallel-strict", ("--parallel", "--parallel-strict")),
            (
                "multipar",
                (
                    "--parallel",
                    "--multipar",
                    "--nointratileopt",
                    "--noprevector",
                    "--nounrolljam",
                ),
            ),
            (
                "multipar-strict",
                (
                    "--parallel",
                    "--multipar",
                    "--parallel-strict",
                    "--nointratileopt",
                    "--noprevector",
                    "--nounrolljam",
                ),
            ),
            ("vector-hint", ("--vector",)),
            ("vector-strict", ("--vector", "--vector-strict")),
            ("parallel-current", ("--parallel-current", "1")),
            ("vector-current", ("--vector-current", "1")),
        ):
            if "--multipar" in consumer_args:
                consumer_args = (*consumer_args, "--nodiamond-tile")
            vector_current_rejected = consumer_name == "vector-current"
            if consumer_name in ("vector-hint", "vector-strict"):
                vector_status = "status=skipped reason=no-hint"
            elif vector_current_rejected:
                vector_status = (
                    "status=rejected source=explicit-current "
                    "reason=not-certifiable-or-non-innermost"
                )
            else:
                vector_status = None
            cases.append(
                Case(
                    name=f"identity-mixed-depth{iss_name}-{consumer_name}",
                    fixture=MATMUL_INIT,
                    args=("--identity-tiled", *iss_args, *consumer_args),
                    expected_route=(
                        "rejected" if vector_current_rejected else "permutable-band"
                    ),
                    expect_success=not vector_current_rejected,
                    expected_vector_status=vector_status,
                )
            )
    return cases


def run_case(polopt: Path, case: Case, timeout: int) -> str | None:
    if "--second-level-tile" in case.args:
        return f"{case.name}: non-second-level matrix contains --second-level-tile"
    env = os.environ.copy()
    env.setdefault("COMPCERT_CONFIG", str(ROOT / "tests" / "pluto" / "polcert.ini"))
    try:
        with tempfile.TemporaryDirectory(prefix="polcert-one-level-route-") as tmp:
            proc = subprocess.run(
                [str(polopt), *case.args, str(case.fixture)],
                cwd=tmp,
                env=env,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
    except subprocess.TimeoutExpired:
        return f"{case.name}: timed out after {timeout}s"

    output = proc.stdout + proc.stderr
    if not case.expect_success:
        route_lines = [
            line.strip()
            for line in proc.stderr.splitlines()
            if line.strip().startswith(ROUTE_PREFIX)
        ]
        expected_vector = f"{VECTOR_PREFIX}{case.expected_vector_status}"
        if proc.returncode == 0:
            return f"{case.name}: expected explicit vector rejection\n{output}"
        if not any(
            marker in output
            for marker in (
                "Parallel validation failed",
                "non-innermost vector loop, or no vector loop",
            )
        ):
            return f"{case.name}: missing explicit validation failure\n{output}"
        if route_lines:
            return f"{case.name}: vector rejection leaked tiling route {route_lines!r}\n{output}"
        if proc.stderr.count(expected_vector) != 1:
            return f"{case.name}: missing unique vector rejection telemetry\n{output}"
        if GENERAL_FALLBACK_ROUTE in proc.stderr or "status=applied" in proc.stderr:
            return f"{case.name}: explicit rejection leaked an accepted route\n{output}"
        if "== Optimized Loop ==" in proc.stdout or "[alarm]" in proc.stderr:
            return f"{case.name}: explicit rejection produced fallback output\n{output}"
        return None
    if proc.returncode != 0:
        return (
            f"{case.name}: expected a completed one-level route, got exit "
            f"{proc.returncode}\n{output}"
        )
    if "== Optimized Loop ==" not in proc.stdout:
        return f"{case.name}: optimized loop is missing\n{output}"
    route_lines = [
        line.strip()
        for line in proc.stderr.splitlines()
        if line.strip().startswith(ROUTE_PREFIX)
    ]
    if GENERAL_FALLBACK_ROUTE in route_lines:
        return f"{case.name}: one-level route used general fallback\n{output}"
    expected_route = f"{ROUTE_PREFIX}{case.expected_route}"
    if route_lines != [expected_route]:
        return (
            f"{case.name}: expected only {expected_route!r}, got "
            f"{route_lines!r}\n{output}"
        )
    has_alarm = "[alarm]" in proc.stderr
    if has_alarm != case.expect_alarm:
        return (
            f"{case.name}: expected alarm={case.expect_alarm}, got "
            f"alarm={has_alarm}\n{output}"
        )
    vector_lines = [
        line.strip()
        for line in proc.stderr.splitlines()
        if line.strip().startswith(VECTOR_PREFIX)
    ]
    expected_vector_lines = (
        []
        if case.expected_vector_status is None
        else [f"{VECTOR_PREFIX}{case.expected_vector_status}"]
    )
    if vector_lines != expected_vector_lines:
        return (
            f"{case.name}: expected vector telemetry {expected_vector_lines!r}, "
            f"got {vector_lines!r}\n{output}"
        )
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--polopt", default="./polopt")
    ap.add_argument("--timeout", type=int, default=180)
    args = ap.parse_args()

    polopt = Path(args.polopt).resolve()
    if not polopt.is_file():
        raise SystemExit(f"missing polopt: {polopt}")
    missing = [case.fixture for case in route_cases() if not case.fixture.is_file()]
    if missing:
        raise SystemExit(f"missing fixtures: {sorted(set(missing))}")

    failures: list[str] = []
    cases = route_cases()
    names = [case.name for case in cases]
    invalid_routes = {
        case.expected_route
        for case in cases
        if case.expected_route not in ("permutable-band", "rejected")
    }
    if len(cases) != 90:
        failures.append(f"matrix contains {len(cases)} cases, expected 90")
    if len(set(names)) != len(names):
        failures.append("matrix contains duplicate case names")
    if invalid_routes:
        failures.append(f"matrix contains invalid expected routes: {sorted(invalid_routes)}")
    for case in cases:
        if case.expect_alarm:
            failures.append(
                f"{case.name}: non-second-level matrix must not expect an alarm"
            )
        if case.expect_success != (case.expected_route == "permutable-band"):
            failures.append(
                f"{case.name}: success/route expectation is inconsistent"
            )
    for case in cases:
        failure = run_case(polopt, case, args.timeout)
        print(f"[non-second-level-routes] {case.name}: {'PASS' if failure is None else 'FAIL'}")
        if failure is not None:
            failures.append(failure)

    if failures:
        print("[non-second-level-routes] FAIL")
        for failure in failures:
            print(failure)
        return 1
    accepted = sum(case.expected_route == "permutable-band" for case in cases)
    rejected = len(cases) - accepted
    if accepted != 84 or rejected != 6:
        print(
            "[non-second-level-routes] FAIL: "
            f"expected 84 completed compositions/6 explicit vector rejections, "
            f"got {accepted}/{rejected}"
        )
        return 1
    print(
        f"[non-second-level-routes] OK "
        f"({accepted} permutable-band compositions, {rejected} explicit vector "
        "rejections, 0 general fallbacks)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
