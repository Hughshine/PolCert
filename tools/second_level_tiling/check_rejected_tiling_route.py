#!/usr/bin/env python3
"""Check malformed tilings and distinguish failures in later consumers."""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import subprocess


REJECTED_ROUTE = "[tiling-validation] route=rejected"
BAND_ROUTE = "[tiling-validation] route=permutable-band"
NO_VECTOR_HINT = "[vector-validation] status=skipped reason=no-hint"
PARALLEL_REJECTION = (
    "[parallel-validation] status=rejected source=explicit-current "
    "reason=not-certifiable-or-out-of-range"
)
VECTOR_REJECTION = (
    "[vector-validation] status=rejected source=explicit-current "
    "reason=not-certifiable-or-non-innermost"
)
TILE_LINK_MUTATION = "[rejecting-pluto] corrupted one tiling tile-link"
FINAL_AFFINE_MUTATION = "[rejecting-pluto] reversed "


@dataclass(frozen=True)
class MalformedTilingCase:
    name: str
    fixture: Path
    args: tuple[str, ...]


@dataclass(frozen=True)
class ConsumerFailureCase:
    name: str
    fixture: Path
    args: tuple[str, ...]
    rejection: str


def route_lines(stderr: str) -> list[str]:
    return [
        line.strip()
        for line in stderr.splitlines()
        if line.strip().startswith("[tiling-validation] route=")
    ]


def run_polopt(
    *,
    polopt: Path,
    fixture: Path,
    args: tuple[str, ...],
    timeout: int,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(polopt), *args, str(fixture)],
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env=os.environ.copy() if env is None else env,
    )


def malformed_tiling_cases(root: Path) -> list[MalformedTilingCase]:
    symbolic = root / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop"
    mixed_depth = root / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
    diamond = (
        root
        / "tools"
        / "parallel_current"
        / "fixtures"
        / "diamond-example-inner-batch.loop"
    )
    cases: list[MalformedTilingCase] = []
    for name, fixture, args in (
        ("ordinary", symbolic, ()),
        ("identity-mixed-depth", mixed_depth, ("--identity-tiled",)),
        ("second-level", symbolic, ("--second-level-tile",)),
        (
            "second-level-identity-mixed-depth",
            mixed_depth,
            ("--second-level-tile", "--identity-tiled"),
        ),
        ("diamond", diamond, ("--diamond-tile",)),
        ("full-diamond", diamond, ("--full-diamond-tile",)),
        (
            "second-level-diamond",
            diamond,
            ("--second-level-tile", "--diamond-tile"),
        ),
        (
            "second-level-full-diamond",
            diamond,
            ("--second-level-tile", "--full-diamond-tile"),
        ),
    ):
        cases.append(MalformedTilingCase(name, fixture, args))
        cases.append(MalformedTilingCase(f"{name}-iss", fixture, (*args, "--iss")))
    return cases


def consumer_failure_cases(root: Path) -> list[ConsumerFailureCase]:
    symbolic = root / "tools" / "second_level_tiling" / "fixtures" / "symbolic-independent-2d.loop"
    mixed_depth = root / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
    diamond = (
        root
        / "tools"
        / "parallel_current"
        / "fixtures"
        / "diamond-example-inner-batch.loop"
    )
    producers = (
        ("ordinary", symbolic, ()),
        ("second-level-iss", symbolic, ("--second-level-tile", "--iss")),
        ("identity-mixed-depth", mixed_depth, ("--identity-tiled",)),
        (
            "second-level-identity-mixed-depth-iss",
            mixed_depth,
            ("--second-level-tile", "--identity-tiled", "--iss"),
        ),
        ("diamond", diamond, ("--diamond-tile",)),
        ("full-diamond-iss", diamond, ("--full-diamond-tile", "--iss")),
    )
    cases: list[ConsumerFailureCase] = []
    for name, fixture, producer_args in producers:
        cases.append(
            ConsumerFailureCase(
                f"{name}-parallel-current",
                fixture,
                (*producer_args, "--parallel-current", "999"),
                PARALLEL_REJECTION,
            )
        )
        cases.append(
            ConsumerFailureCase(
                f"{name}-vector-current",
                fixture,
                (*producer_args, "--vector-current", "999"),
                VECTOR_REJECTION,
            )
        )
    return cases


def assert_no_alternate_route(label: str, stderr: str) -> None:
    if BAND_ROUTE in stderr:
        raise AssertionError(f"{label} malformed candidate reported permutable-band")
    if "fallback" in stderr.lower():
        raise AssertionError(f"{label} reported a forbidden fallback route")


def check_malformed_tiling_cases(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "tiling"
    cases = malformed_tiling_cases(root)
    for case in cases:
        proc = run_polopt(
            polopt=polopt,
            fixture=case.fixture,
            args=case.args,
            timeout=timeout,
            env=env,
        )
        label = f"malformed {case.name}"
        if proc.returncode == 0:
            raise AssertionError(
                f"{label} did not fail closed\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if route_lines(proc.stderr) != [REJECTED_ROUTE]:
            raise AssertionError(
                f"{label} did not report exactly one rejected tiling route\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        assert_no_alternate_route(label, proc.stderr)
        if proc.stderr.count(TILE_LINK_MUTATION) != 1:
            raise AssertionError(f"{label} did not perform exactly one tile-link mutation")
        if proc.stderr.count("[alarm]") != 1:
            raise AssertionError(f"{label} did not report exactly one rejection alarm")
        if "== Optimized Loop ==" in proc.stdout:
            raise AssertionError(f"{label} emitted output after rejecting tiling")
    return len(cases)


def check_integrated_direct_checker_rejection(
    *,
    polopt: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> None:
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(
        root / "tools" / "tiling_routes" / "frozen_nonpermutable_pluto.py"
    )
    proc = run_polopt(
        polopt=polopt,
        fixture=(
            root
            / "tools"
            / "tiling_routes"
            / "fixtures"
            / "nonpermutable-band.loop"
        ),
        args=(),
        timeout=timeout,
        env=env,
    )
    label = "integrated direct-checker nonpermutable band"
    if proc.returncode == 0:
        raise AssertionError(f"{label} unexpectedly succeeded")
    if route_lines(proc.stderr) != [REJECTED_ROUTE]:
        raise AssertionError(
            f"{label} did not report exactly one rejected route\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    if proc.stderr.count("[frozen-nonpermutable-pluto]") != 2:
        raise AssertionError(f"{label} did not replace both Pluto phase outputs")
    assert_no_alternate_route(label, proc.stderr)
    if proc.stderr.count("[alarm]") != 1:
        raise AssertionError(f"{label} did not report exactly one alarm")
    if "== Optimized Loop ==" in proc.stdout:
        raise AssertionError(f"{label} emitted output after rejection")


def check_consumer_failure_cases(
    *,
    polopt: Path,
    root: Path,
    timeout: int,
) -> int:
    cases = consumer_failure_cases(root)
    for case in cases:
        proc = run_polopt(
            polopt=polopt,
            fixture=case.fixture,
            args=case.args,
            timeout=timeout,
        )
        label = f"consumer failure {case.name}"
        if proc.returncode == 0:
            raise AssertionError(f"{label} unexpectedly succeeded")
        if route_lines(proc.stderr):
            raise AssertionError(
                f"{label} was mislabeled as a tiling outcome: "
                f"{route_lines(proc.stderr)!r}"
            )
        if proc.stderr.count(case.rejection) != 1:
            raise AssertionError(f"{label} omitted its unique consumer rejection")
        if "fallback" in proc.stderr.lower() or BAND_ROUTE in proc.stderr:
            raise AssertionError(f"{label} leaked an accepted tiling route")
        if proc.stderr.count("[alarm]") != 1:
            raise AssertionError(
                f"{label} reported {proc.stderr.count('[alarm]')} alarms, "
                "expected 1"
            )
        if "== Optimized Loop ==" in proc.stdout:
            raise AssertionError(f"{label} emitted output after rejection")
        if "validation failed" not in proc.stderr.lower():
            raise AssertionError(f"{label} omitted its validation failure")
    return len(cases)


def check_malformed_tiling_with_explicit_consumers(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    all_cases = {case.name: case for case in malformed_tiling_cases(root)}
    producer_names = (
        "ordinary",
        "identity-mixed-depth-iss",
        "second-level",
        "second-level-identity-mixed-depth-iss",
        "diamond",
        "full-diamond-iss",
        "second-level-diamond",
        "second-level-full-diamond-iss",
    )
    consumers = (
        ("parallel-current", ("--parallel-current", "999"), PARALLEL_REJECTION),
        ("vector-current", ("--vector-current", "999"), VECTOR_REJECTION),
    )
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "tiling"
    count = 0
    for producer_name in producer_names:
        producer = all_cases[producer_name]
        for consumer_name, consumer_args, consumer_rejection in consumers:
            proc = run_polopt(
                polopt=polopt,
                fixture=producer.fixture,
                args=(*producer.args, *consumer_args),
                timeout=timeout,
                env=env,
            )
            label = f"malformed {producer_name} with {consumer_name}"
            if proc.returncode == 0:
                raise AssertionError(f"{label} did not fail closed")
            if route_lines(proc.stderr) != [REJECTED_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve its unique producer rejection\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            if consumer_rejection in proc.stderr:
                raise AssertionError(f"{label} was mislabeled as a consumer rejection")
            assert_no_alternate_route(label, proc.stderr)
            if proc.stderr.count(TILE_LINK_MUTATION) != 1:
                raise AssertionError(f"{label} did not mutate exactly one tile link")
            if proc.stderr.count("[alarm]") != 1:
                raise AssertionError(f"{label} did not report exactly one alarm")
            if "== Optimized Loop ==" in proc.stdout:
                raise AssertionError(f"{label} emitted output after rejection")
            count += 1
    return count


def check_malformed_tiling_with_hinted_consumers(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    all_cases = {case.name: case for case in malformed_tiling_cases(root)}
    producer_names = (
        "ordinary",
        "diamond",
        "second-level-full-diamond-iss",
    )
    consumers = (
        (
            "parallel",
            (
                "--parallel",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "parallel-strict",
            (
                "--parallel",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "multipar",
            (
                "--parallel",
                "--multipar",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "multipar-strict",
            (
                "--parallel",
                "--multipar",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
        ),
        (
            "vector",
            (
                "--vector",
                "--smartfuse",
                "--nointratileopt",
                "--nounrolljam",
                "--rar",
                "--noparallel",
            ),
        ),
        (
            "vector-strict",
            (
                "--vector",
                "--vector-strict",
                "--smartfuse",
                "--nointratileopt",
                "--nounrolljam",
                "--rar",
                "--noparallel",
            ),
        ),
    )
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "tiling"
    count = 0
    for producer_name in producer_names:
        producer = all_cases[producer_name]
        explicit_phase_args = (
            ()
            if any(
                flag in producer.args
                for flag in ("--diamond-tile", "--full-diamond-tile")
            )
            else ("--nodiamond-tile",)
        )
        for consumer_name, consumer_args in consumers:
            proc = run_polopt(
                polopt=polopt,
                fixture=producer.fixture,
                args=(*producer.args, *consumer_args, *explicit_phase_args),
                timeout=timeout,
                env=env,
            )
            label = f"malformed {producer_name} with hinted {consumer_name}"
            if proc.returncode == 0:
                raise AssertionError(f"{label} did not fail closed")
            if route_lines(proc.stderr) != [REJECTED_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve its unique producer rejection\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            if (
                "[parallel-validation] status=rejected" in proc.stderr
                or "[vector-validation] status=rejected" in proc.stderr
            ):
                raise AssertionError(
                    f"{label} was mislabeled as a consumer rejection\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            assert_no_alternate_route(label, proc.stderr)
            if proc.stderr.count(TILE_LINK_MUTATION) < 1:
                raise AssertionError(f"{label} did not mutate a tile link")
            if proc.stderr.count("[alarm]") != 1:
                raise AssertionError(f"{label} did not report exactly one alarm")
            if "== Optimized Loop ==" in proc.stdout:
                raise AssertionError(f"{label} emitted output after rejection")
            count += 1
    return count


def check_final_affine_failure_cases(
    *,
    polopt: Path,
    wrapper: Path,
    real_pluto: Path,
    root: Path,
    timeout: int,
) -> int:
    diamond = (
        root
        / "tools"
        / "parallel_current"
        / "fixtures"
        / "diamond-example-inner-batch.loop"
    )
    producer_cases = (
        ("diamond", ("--diamond-tile",)),
        ("diamond-iss", ("--diamond-tile", "--iss")),
        ("full-diamond", ("--full-diamond-tile",)),
        ("full-diamond-iss", ("--full-diamond-tile", "--iss")),
        (
            "second-level-diamond",
            ("--second-level-tile", "--diamond-tile"),
        ),
        (
            "second-level-diamond-iss",
            ("--second-level-tile", "--diamond-tile", "--iss"),
        ),
        (
            "second-level-full-diamond",
            ("--second-level-tile", "--full-diamond-tile"),
        ),
        (
            "second-level-full-diamond-iss",
            ("--second-level-tile", "--full-diamond-tile", "--iss"),
        ),
    )
    consumers = (
        ("sequential", (), None, 1),
        (
            "parallel-current",
            ("--parallel-current", "0"),
            "[parallel-validation] status=rejected",
            1,
        ),
        (
            "vector-current",
            ("--vector-current", "0"),
            "[vector-validation] status=rejected",
            1,
        ),
        (
            "parallel-hint-strict",
            (
                "--parallel",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
            "[parallel-validation] status=rejected",
            2,
        ),
        (
            "multipar-hint-strict",
            (
                "--parallel",
                "--multipar",
                "--parallel-strict",
                "--innerpar",
                "--smartfuse",
                "--nointratileopt",
                "--noprevector",
                "--nounrolljam",
                "--rar",
            ),
            "[parallel-validation] status=rejected",
            2,
        ),
        (
            "vector-hint-strict",
            (
                "--vector",
                "--vector-strict",
                "--smartfuse",
                "--nointratileopt",
                "--nounrolljam",
                "--rar",
                "--noparallel",
            ),
            "[vector-validation] status=rejected",
            2,
        ),
    )
    env = os.environ.copy()
    env["POLCERT_REAL_PLUTO"] = str(real_pluto)
    env["POLCERT_PLUTO"] = str(wrapper)
    env["POLCERT_REJECTING_PLUTO_MODE"] = "final-affine"
    count = 0
    for name, producer_args in producer_cases:
        for (
            consumer_name,
            consumer_args,
            consumer_rejection,
            expected_mutations,
        ) in consumers:
            proc = run_polopt(
                polopt=polopt,
                fixture=diamond,
                args=(*producer_args, *consumer_args),
                timeout=timeout,
                env=env,
            )
            label = f"final affine failure {name} with {consumer_name}"
            if proc.returncode == 0:
                raise AssertionError(
                    f"{label} unexpectedly accepted the malformed final schedule"
                )
            if route_lines(proc.stderr) != [BAND_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve the successful tiling-leg route\n"
                    f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
                )
            if consumer_rejection is not None and consumer_rejection in proc.stderr:
                raise AssertionError(
                    f"{label} was mislabeled as a consumer rejection"
                )
            if REJECTED_ROUTE in proc.stderr or "fallback" in proc.stderr.lower():
                raise AssertionError(f"{label} mislabeled the final affine rejection")
            if proc.stderr.count(FINAL_AFFINE_MUTATION) != expected_mutations:
                raise AssertionError(
                    f"{label} performed "
                    f"{proc.stderr.count(FINAL_AFFINE_MUTATION)} final-schedule "
                    f"mutations, expected {expected_mutations}"
                )
            if proc.stderr.count("[alarm]") != 1:
                raise AssertionError(
                    f"{label} did not report exactly one validation alarm"
                )
            if "== Optimized Loop ==" in proc.stdout:
                raise AssertionError(
                    f"{label} emitted output after a validation alarm"
                )
            count += 1
    return count


def check_rejected_tiling_route(
    *,
    polopt: Path,
    fixture: Path,
    timeout: int,
) -> None:
    root = Path(__file__).resolve().parents[2]
    wrapper = Path(__file__).resolve().with_name("rejecting_pluto.py")
    real_pluto = Path(
        os.environ.get(
            "POLCERT_REAL_PLUTO",
            os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"),
        )
    ).resolve()
    if not fixture.is_file():
        raise AssertionError(f"missing legacy rejection fixture: {fixture}")

    malformed_count = check_malformed_tiling_cases(
        polopt=polopt,
        wrapper=wrapper,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )
    check_integrated_direct_checker_rejection(
        polopt=polopt,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )

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
    if scalar_only.returncode == 0:
        raise AssertionError("scalar-only tiling request did not fail closed")
    if route_lines(scalar_only.stderr) != [REJECTED_ROUTE]:
        raise AssertionError(
            "a tiling request with no non-scalar statement was not explicitly rejected"
        )
    if scalar_only.stderr.count("[alarm]") != 1:
        raise AssertionError("scalar-only rejection omitted its unique alarm")
    if "== Optimized Loop ==" in scalar_only.stdout:
        raise AssertionError("scalar-only rejection emitted optimized output")

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
                raise AssertionError(f"{label} conservative vector skip failed")
            if route_lines(strict.stderr) != [BAND_ROUTE]:
                raise AssertionError(
                    f"{label} did not preserve its verified band route"
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

    consumer_failure_count = check_consumer_failure_cases(
        polopt=polopt,
        root=root,
        timeout=timeout,
    )
    malformed_consumer_count = check_malformed_tiling_with_explicit_consumers(
        polopt=polopt,
        wrapper=wrapper,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )
    malformed_hinted_consumer_count = (
        check_malformed_tiling_with_hinted_consumers(
            polopt=polopt,
            wrapper=wrapper,
            real_pluto=real_pluto,
            root=root,
            timeout=timeout,
        )
    )
    final_affine_count = check_final_affine_failure_cases(
        polopt=polopt,
        wrapper=wrapper,
        real_pluto=real_pluto,
        root=root,
        timeout=timeout,
    )

    print(
        "rejected tiling route: PASS "
        f"({malformed_count} malformed tilings fail closed, scalar-only fails "
        "closed, one integrated nonpermutable candidate reaches the direct "
        "checker and is rejected once, four vector skips preserve verified tilings, "
        f"{consumer_failure_count} consumer failures do not alter the tiling "
        f"outcome, {malformed_consumer_count} malformed producer/consumer "
        "combinations preserve the producer rejection, "
        f"{malformed_hinted_consumer_count} malformed producer/hinted-consumer "
        f"combinations preserve the producer rejection, and {final_affine_count} "
        "final-affine failures preserve "
        "the successful tiling-leg route and fail closed)"
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
