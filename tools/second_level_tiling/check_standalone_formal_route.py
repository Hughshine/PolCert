#!/usr/bin/env python3
"""Exercise standalone formal validation at and before the tiling phase boundary."""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile


BAND_ROUTE = "[tiling-validation] route=permutable-band"

AFFINE_PLUTO_FLAGS = [
    "--dumpscop",
    "--readscop",
    "--nointratileopt",
    "--nodiamond-tile",
    "--noprevector",
    "--smartfuse",
    "--nounrolljam",
    "--noparallel",
    "--notile",
    "--rar",
]

TILING_PLUTO_FLAGS = [
    "--dumpscop",
    "--readscop",
    "--identity",
    "--tile",
    "--second-level-tile",
    "--nointratileopt",
    "--nodiamond-tile",
    "--noprevector",
    "--nounrolljam",
    "--noparallel",
    "--rar",
]


def run(
    cmd: list[str],
    *,
    cwd: Path,
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def require_success(proc: subprocess.CompletedProcess[str], label: str) -> None:
    if proc.returncode != 0:
        raise AssertionError(
            f"{label} failed with exit {proc.returncode}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )


def run_pluto_phase(
    *,
    pluto: Path,
    flags: list[str],
    input_scop: Path,
    timeout: int,
    label: str,
) -> Path:
    scheduled = run(
        [str(pluto), *flags, input_scop.name],
        cwd=input_scop.parent,
        timeout=timeout,
    )
    require_success(scheduled, label)
    output_scop = input_scop.with_name(
        f"{input_scop.name}.afterscheduling.scop"
    )
    if not output_scop.is_file():
        raise AssertionError(f"{label} omitted its OpenScop output: {output_scop}")
    return output_scop


def validate_expected_route(
    *,
    polopt: Path,
    before: Path,
    after: Path,
    expected_route: str,
    timeout: int,
    label: str,
) -> None:
    validated = run(
        [
            str(polopt),
            "--second-level-tile",
            "--validate-tiling-openscop",
            str(before),
            str(after),
        ],
        cwd=before.parent,
        timeout=timeout,
    )
    require_success(validated, label)
    if "overall: PASS" not in validated.stdout:
        raise AssertionError(
            f"{label} omitted the structural PASS report\n"
            f"stdout:\n{validated.stdout}\nstderr:\n{validated.stderr}"
        )
    if "formal: PASS" not in validated.stdout:
        raise AssertionError(
            f"{label} did not execute or pass the formal checker\n"
            f"stdout:\n{validated.stdout}\nstderr:\n{validated.stderr}"
        )
    route_lines = [
        line.strip()
        for line in validated.stderr.splitlines()
        if line.strip().startswith("[tiling-validation] route=")
    ]
    if route_lines != [expected_route]:
        raise AssertionError(
            f"{label} reported routes {route_lines!r}, expected exactly "
            f"{[expected_route]!r}\n"
            f"stdout:\n{validated.stdout}\nstderr:\n{validated.stderr}"
        )
    if "[alarm]" in validated.stderr:
        raise AssertionError(
            f"{label} reported an alarm\n"
            f"stdout:\n{validated.stdout}\nstderr:\n{validated.stderr}"
        )


def check_standalone_formal_route(
    *,
    polopt: Path,
    loop_fixture: Path,
    timeout: int,
) -> None:
    pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
    if not pluto.is_file():
        raise AssertionError(f"Pluto executable not found: {pluto}")

    with tempfile.TemporaryDirectory(prefix="polcert-standalone-tiling-") as tmp:
        tmp_path = Path(tmp)
        extracted = run(
            [str(polopt), "--extract-only", str(loop_fixture)],
            cwd=tmp_path,
            timeout=timeout,
        )
        require_success(extracted, "loop extraction")
        source = tmp_path / "source.scop"
        source.write_text(extracted.stdout, encoding="utf-8")

        affine_output = run_pluto_phase(
            pluto=pluto,
            flags=AFFINE_PLUTO_FLAGS,
            input_scop=source,
            timeout=timeout,
            label="Pluto affine midpoint scheduling",
        )
        midpoint = tmp_path / "midpoint.scop"
        midpoint.write_bytes(affine_output.read_bytes())
        posttile = run_pluto_phase(
            pluto=pluto,
            flags=TILING_PLUTO_FLAGS,
            input_scop=midpoint,
            timeout=timeout,
            label="Pluto phase-aligned second-level identity tiling",
        )
        validate_expected_route(
            polopt=polopt,
            before=midpoint,
            after=posttile,
            expected_route=BAND_ROUTE,
            timeout=timeout,
            label="phase-aligned standalone formal tiling validation",
        )

        direct_source = tmp_path / "direct-source.scop"
        direct_source.write_text(extracted.stdout, encoding="utf-8")
        direct_posttile = run_pluto_phase(
            pluto=pluto,
            flags=TILING_PLUTO_FLAGS,
            input_scop=direct_source,
            timeout=timeout,
            label="Pluto direct source-like second-level identity tiling",
        )
        validate_expected_route(
            polopt=polopt,
            before=direct_source,
            after=direct_posttile,
            expected_route=BAND_ROUTE,
            timeout=timeout,
            label="source-like standalone formal band validation",
        )

    # This frozen two-statement Pluto output omits a globally zero trailing
    # schedule row when the target schedule is canonicalized.
    fixtures = Path(__file__).resolve().parent / "fixtures"
    validate_expected_route(
        polopt=polopt,
        before=fixtures / "fusion7-second-level-zero-normalized.mid.openscop",
        after=fixtures / "fusion7-second-level-zero-normalized.post.openscop",
        expected_route=BAND_ROUTE,
        timeout=timeout,
        label="trailing-zero-normalized standalone formal validation",
    )
