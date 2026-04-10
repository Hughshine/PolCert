#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]


def load_manifest(path: pathlib.Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"manifest must be a JSON object: {path}")
    return data


def load_fixture_map(manifest_path: pathlib.Path, data: dict[str, object]) -> dict[str, pathlib.Path]:
    raw_fixtures = data.get("fixtures", {})
    if not isinstance(raw_fixtures, dict):
        raise SystemExit("fixtures must be an object mapping names to relative paths")
    fixtures: dict[str, pathlib.Path] = {}
    for name, relpath in raw_fixtures.items():
        if not isinstance(name, str) or not isinstance(relpath, str):
            raise SystemExit("fixtures must map string names to string paths")
        fixture_path = (manifest_path.parent / relpath).resolve()
        if not fixture_path.is_file():
            raise SystemExit(f"fixture not found: {fixture_path}")
        fixtures[name] = fixture_path
    return fixtures


def run_polopt(polopt: pathlib.Path, loop_path: pathlib.Path, args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(polopt), *args, str(loop_path)],
        cwd=str(ROOT),
        text=True,
        capture_output=True,
        check=False,
    )


def evaluate_check(
    fixtures: dict[str, pathlib.Path],
    polopt: pathlib.Path,
    spec: dict[str, object],
) -> str | None:
    if not isinstance(spec.get("name"), str):
        raise SystemExit("check name must be a string")
    if not isinstance(spec.get("fixture"), str):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: fixture must be a string")
    if not isinstance(spec.get("expect"), str):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: expect must be a string")
    if not isinstance(spec.get("needle"), str):
        raise SystemExit(f"{spec.get('name', '<unnamed>')}: needle must be a string")
    raw_args = spec.get("args", [])
    if not isinstance(raw_args, list) or not all(isinstance(arg, str) for arg in raw_args):
        raise SystemExit(f"{spec['name']}: args must be a string list")
    fixture_name = str(spec["fixture"])
    if fixture_name not in fixtures:
        raise SystemExit(f"{spec['name']}: unknown fixture {fixture_name!r}")

    proc = run_polopt(polopt, fixtures[fixture_name], list(raw_args))
    expected = str(spec["expect"])
    needle = str(spec["needle"])
    if expected == "success":
        if proc.returncode != 0:
            return f"{spec['name']}: expected success, got exit {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        if needle not in proc.stdout:
            return f"{spec['name']}: missing {needle!r} in stdout\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        return None
    if expected == "failure":
        if proc.returncode == 0:
            return f"{spec['name']}: expected failure, but command succeeded\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        haystack = proc.stderr + proc.stdout
        if needle not in haystack:
            return f"{spec['name']}: missing {needle!r} in failure output\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        return None
    raise SystemExit(f"{spec['name']}: unsupported expect value {expected!r}")


def run_manifest_suite(*, manifest_path: pathlib.Path, polopt: pathlib.Path) -> int:
    data = load_manifest(manifest_path)
    suite_name = data.get("suite_name", "POLOPT-FLAG-SUITE")
    if not isinstance(suite_name, str):
        raise SystemExit("suite_name must be a string")
    raw_checks = data.get("checks", [])
    if not isinstance(raw_checks, list) or not all(isinstance(spec, dict) for spec in raw_checks):
        raise SystemExit("checks must be a list of objects")

    fixtures = load_fixture_map(manifest_path, data)
    failures: list[str] = []
    for spec in raw_checks:
        failure = evaluate_check(fixtures, polopt, spec)
        if failure is not None:
            failures.append(failure)

    if failures:
        print(f"[{suite_name}] FAIL")
        for failure in failures:
            print(failure)
        return 1

    print(f"[{suite_name}] OK")
    return 0
