#!/usr/bin/env python3
"""Check direct tiling validation with interleaved scalar schedule components."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tools" / "tiling_routes" / "fixtures"
MIDPOINT = FIXTURES / "fusion5-scalar-interleaved.midtransform.scop"
POSTTILE = FIXTURES / "fusion5-scalar-interleaved.posttile.scop"
EXPECTED_HASHES = {
    MIDPOINT.name: "4a52ec690857d1d97028a260f30d03cb301af7301b5c7ab0fe58f43ce93b5e9a",
    POSTTILE.name: "253abb02692581bc2d70e14d15f83d71cdeb0cbbb1adea7a5a7888e44fbd3e38",
}


@dataclass
class Scattering:
    header_index: int
    header: list[int]
    row_indices: list[int]
    rows: list[list[int]]

    @property
    def output_dims(self) -> int:
        return self.header[2]


def numeric_prefix(line: str) -> list[int]:
    return [int(token) for token in line.partition("##")[0].split()]


def format_numbers(values: list[int]) -> str:
    return " ".join(f"{value:4d}" for value in values)


def first_scattering(lines: list[str]) -> Scattering:
    try:
        marker = lines.index("SCATTERING")
    except ValueError as exc:
        raise AssertionError("fixture has no SCATTERING relation") from exc
    header_index = marker + 1
    header = numeric_prefix(lines[header_index])
    if len(header) != 6:
        raise AssertionError(f"unexpected scattering header: {header}")

    row_indices: list[int] = []
    rows: list[list[int]] = []
    index = header_index + 1
    while len(rows) < header[0] and index < len(lines):
        stripped = lines[index].strip()
        if stripped and not stripped.startswith("#"):
            row = numeric_prefix(lines[index])
            if len(row) != header[1]:
                raise AssertionError(
                    f"scattering row has {len(row)} columns, expected {header[1]}"
                )
            row_indices.append(index)
            rows.append(row)
        index += 1
    if len(rows) != header[0]:
        raise AssertionError(
            f"scattering relation has {len(rows)} rows, expected {header[0]}"
        )
    return Scattering(header_index, header, row_indices, rows)


def scalar_dimensions(scattering: Scattering) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    output_dims = scattering.output_dims
    for row_position, row in enumerate(scattering.rows):
        if row[0] != 0:
            continue
        output = row[1 : 1 + output_dims]
        non_output = row[1 + output_dims : -1]
        if any(non_output):
            continue
        for dimension, coefficient in enumerate(output):
            if coefficient == -1 and all(
                value == 0
                for position, value in enumerate(output)
                if position != dimension
            ):
                result.append((dimension, row_position))
    return result


def require_expected_scalar_shape(scattering: Scattering) -> None:
    dimensions = [dimension for dimension, _ in scalar_dimensions(scattering)]
    if dimensions != [1, 4]:
        raise AssertionError(
            "frozen posttile no longer has scalar components at c2 and c5: "
            f"{dimensions}"
        )


def mutate_scalar_constant(source: list[str]) -> list[str]:
    lines = source.copy()
    scattering = first_scattering(lines)
    require_expected_scalar_shape(scattering)
    _, row_position = scalar_dimensions(scattering)[0]
    row = scattering.rows[row_position].copy()
    row[-1] += 2
    lines[scattering.row_indices[row_position]] = format_numbers(row)
    return lines


def mutate_scalar_position(source: list[str]) -> list[str]:
    lines = source.copy()
    scattering = first_scattering(lines)
    require_expected_scalar_shape(scattering)
    scalar_dimension = scalar_dimensions(scattering)[0][0]
    band_dimension = scalar_dimension + 1
    mutated_rows: list[list[int]] = []
    for row in scattering.rows:
        mutated = row.copy()
        left = 1 + scalar_dimension
        right = 1 + band_dimension
        mutated[left], mutated[right] = mutated[right], mutated[left]
        mutated_rows.append(mutated)
    mutated_rows[scalar_dimension], mutated_rows[band_dimension] = (
        mutated_rows[band_dimension],
        mutated_rows[scalar_dimension],
    )
    for row_index, row in zip(scattering.row_indices, mutated_rows):
        lines[row_index] = format_numbers(row)
    return lines


def mutate_noncanonical_output_matrix(source: list[str]) -> list[str]:
    lines = source.copy()
    scattering = first_scattering(lines)
    require_expected_scalar_shape(scattering)
    scalar_dimension = scalar_dimensions(scattering)[0][0]
    band_dimension = scalar_dimension + 1
    for row_index, row in zip(scattering.row_indices, scattering.rows):
        mutated = row.copy()
        left = 1 + scalar_dimension
        right = 1 + band_dimension
        mutated[left], mutated[right] = mutated[right], mutated[left]
        lines[row_index] = format_numbers(mutated)
    return lines


def mutate_scalar_deletion(source: list[str]) -> list[str]:
    lines = source.copy()
    scattering = first_scattering(lines)
    require_expected_scalar_shape(scattering)
    scalar_dimension, scalar_row_position = scalar_dimensions(scattering)[0]
    scalar_row_index = scattering.row_indices[scalar_row_position]
    coefficient_index = 1 + scalar_dimension

    header = scattering.header.copy()
    header[0] -= 1
    header[1] -= 1
    header[2] -= 1
    lines[scattering.header_index] = format_numbers(header)
    for row_index, row in zip(scattering.row_indices, scattering.rows):
        if row_index != scalar_row_index:
            lines[row_index] = format_numbers(
                row[:coefficient_index] + row[coefficient_index + 1 :]
            )
    del lines[scalar_row_index]
    return lines


def check_hashes() -> None:
    for fixture in (MIDPOINT, POSTTILE):
        actual = hashlib.sha256(fixture.read_bytes()).hexdigest()
        expected = EXPECTED_HASHES[fixture.name]
        if actual != expected:
            raise AssertionError(
                f"frozen fixture hash mismatch for {fixture}: "
                f"expected {expected}, got {actual}"
            )


def run_validation(
    polcert: Path,
    before: Path,
    after: Path,
    expected_route: str,
    timeout: int,
) -> str | None:
    try:
        proc = subprocess.run(
            [str(polcert), "--tiling", str(before), str(after)],
            cwd=str(ROOT),
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return f"timed out after {timeout}s"

    output = proc.stdout + proc.stderr
    if expected_route == "import-rejected":
        if proc.returncode == 0:
            return (
                "malformed fixture exited successfully\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if "cannot import" not in output or "not consistent" not in output:
            return (
                "malformed fixture did not fail at the importer boundary\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
        if "[TILING-OK]" in output or "route=permutable-band" in output:
            return f"malformed fixture reached an accepting route:\n{output}"
        if "fallback" in output.lower():
            return f"fallback marker appeared in importer rejection:\n{output}"
        return None

    if expected_route == "permutable-band":
        expected_line = (
            f"[TILING-OK] {after} validates {before} as a tiling-derived "
            "refinement (route=permutable-band)."
        )
        if proc.returncode != 0:
            return (
                f"accepted fixture exited {proc.returncode}\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
    else:
        expected_line = (
            f"[TILING-FAIL] {after} does not validate {before} as a "
            "tiling-derived refinement (route=rejected)."
        )
        if proc.returncode == 0:
            return (
                "rejected fixture exited successfully\n"
                f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )

    if proc.stdout.strip() != expected_line:
        return (
            "telemetry was not the exact expected single line\n"
            f"expected:\n{expected_line}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    if proc.stderr:
        return f"validator-only route emitted stderr:\n{proc.stderr}"
    if "fallback" in output.lower():
        return f"fallback marker appeared in validator output:\n{output}"
    if "== Optimized Loop ==" in output:
        return f"validator-only route emitted optimized output:\n{output}"
    if output.count("(route=") != 1:
        return f"expected exactly one route marker:\n{output}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polcert", default="./polcert")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    polcert = Path(args.polcert).resolve()
    if not polcert.is_file():
        raise SystemExit(f"missing polcert: {polcert}")

    check_hashes()
    source = POSTTILE.read_text(encoding="utf-8").splitlines()
    mutations = (
        ("scalar-row-deleted", mutate_scalar_deletion(source)),
        ("scalar-row-reordered", mutate_scalar_position(source)),
        ("scalar-constant-changed", mutate_scalar_constant(source)),
    )
    malformed = mutate_noncanonical_output_matrix(source)
    failures: list[str] = []
    with tempfile.TemporaryDirectory(prefix="polcert-scalar-interleaved-") as tmp:
        tmp_path = Path(tmp)
        cases: list[tuple[str, Path, str]] = [
            ("frozen-positive", POSTTILE, "permutable-band")
        ]
        for name, mutated_lines in mutations:
            fixture = tmp_path / f"{name}.scop"
            fixture.write_text("\n".join(mutated_lines) + "\n", encoding="utf-8")
            cases.append((name, fixture, "rejected"))
        malformed_fixture = tmp_path / "noncanonical-output-matrix.scop"
        malformed_fixture.write_text(
            "\n".join(malformed) + "\n", encoding="utf-8"
        )
        cases.append(
            (
                "noncanonical-output-matrix",
                malformed_fixture,
                "import-rejected",
            )
        )

        for name, after, expected_route in cases:
            failure = run_validation(
                polcert,
                MIDPOINT,
                after,
                expected_route,
                args.timeout,
            )
            print(
                f"[scalar-interleaved] {name}: "
                f"{'PASS' if failure is None else 'FAIL'}"
            )
            if failure is not None:
                failures.append(f"{name}: {failure}")

    if failures:
        print("[scalar-interleaved] FAIL")
        print("\n".join(failures))
        return 1
    print(
        "[scalar-interleaved] OK "
        "(1 direct acceptance, 3 exact rejections, 1 importer rejection)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
