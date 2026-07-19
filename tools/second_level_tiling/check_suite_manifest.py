#!/usr/bin/env python3
"""Fail-closed structural checks for the second-level tiling test matrix."""

from __future__ import annotations

import json
from pathlib import Path


NESTED_TILE_MARKERS = {"/ 256", "8 *", "32 *"}
BAND_ROUTE = "[tiling-validation] route=permutable-band"
FALLBACK_ROUTE = "[tiling-validation] route=general-fallback"
FALLBACK_CHECK = "second-level-mixed-depth-general-fallback"

BAND_STEMS = {
    "default",
    "parallel-current",
    "parallel-hint",
    "parallel-strict",
    "multipar",
    "multipar-strict",
    "vector-current",
    "vector-hint",
    "vector-strict",
    "fusion",
}
REQUIRED_BAND_ROUTES = {
    f"second-level-{stem}{'-iss' if iss else ''}-band"
    for stem in BAND_STEMS
    for iss in (False, True)
}

IDENTITY_FALLBACK_STEMS = {
    "identity-tiled",
    "identity-parallel-current",
    "identity-vector-current",
    "identity-parallel-hint",
    "identity-parallel-strict",
    "identity-vector-hint",
    "identity-multipar",
    "identity-multipar-strict",
}
DIAMOND_FALLBACK_STEMS = {
    "diamond",
    "full-diamond",
    "diamond-parallel",
    "diamond-vector",
    "diamond-multipar",
    "full-diamond-parallel",
    "full-diamond-vector",
    "full-diamond-multipar",
}
REQUIRED_FALLBACK_ROUTES = {
    f"second-level-{stem}{'-iss' if iss else ''}-general-fallback"
    for stem in IDENTITY_FALLBACK_STEMS | DIAMOND_FALLBACK_STEMS
    for iss in (False, True)
} | {FALLBACK_CHECK}

REQUIRED_NEGATIVES = {
    "second-level-rejects-legacy-alias",
    "second-level-rejects-legacy-alias-iss",
    "second-level-rejects-identity-without-tile",
    "second-level-rejects-notile",
    "second-level-openscop-source-witness-mismatch",
}


def string_list(check: dict[str, object], field: str) -> list[str]:
    raw = check.get(field, [])
    if not isinstance(raw, list) or not all(isinstance(item, str) for item in raw):
        raise AssertionError(f"{check.get('name', '<unnamed>')}: {field} must be a string list")
    return list(raw)


def string_counts(check: dict[str, object], field: str) -> dict[str, int]:
    raw = check.get(field, {})
    if not isinstance(raw, dict):
        raise AssertionError(f"{check.get('name', '<unnamed>')}: {field} must be an object")
    if not all(isinstance(key, str) and isinstance(value, int) for key, value in raw.items()):
        raise AssertionError(f"{check.get('name', '<unnamed>')}: {field} must map strings to integers")
    return dict(raw)


def check_manifest(path: Path) -> None:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("stderr_needles_exactly_once") is not True:
        raise AssertionError("every expected tiling route must be reported exactly once")
    raw_fixtures = data.get("fixtures")
    if not isinstance(raw_fixtures, dict):
        raise AssertionError("fixtures must be an object")
    for name, relpath in raw_fixtures.items():
        if not isinstance(name, str) or not isinstance(relpath, str):
            raise AssertionError("fixture names and paths must be strings")
        fixture_path = (path.parent / relpath).resolve()
        if not fixture_path.is_file():
            raise AssertionError(f"missing fixture {name}: {fixture_path}")

    raw_checks = data.get("checks")
    if not isinstance(raw_checks, list) or not all(isinstance(item, dict) for item in raw_checks):
        raise AssertionError("checks must be a list of objects")

    checks: list[dict[str, object]] = list(raw_checks)
    names = [check.get("name") for check in checks]
    if not all(isinstance(name, str) for name in names):
        raise AssertionError("every check must have a string name")
    if len(set(names)) != len(names):
        raise AssertionError("second-level manifest contains duplicate check names")
    used_fixtures = {
        fixture
        for check in checks
        for field in ("fixture", "input_fixtures")
        for fixture in (
            [check[field]] if isinstance(check.get(field), str)
            else check.get(field, []) if isinstance(check.get(field), list)
            else []
        )
    }
    unused_fixtures = set(raw_fixtures) - used_fixtures
    if unused_fixtures:
        raise AssertionError(f"unused fixture declarations: {sorted(unused_fixtures)!r}")

    tiling_checks = [
        check
        for check in checks
        if check.get("expect") == "success"
        and "--second-level-tile" in string_list(check, "args")
    ]
    band_checks: list[dict[str, object]] = []
    fallback_checks: list[dict[str, object]] = []
    for check in tiling_checks:
        name = str(check["name"])
        args = string_list(check, "args")
        needles = set(string_list(check, "needles"))
        stderr_needles = set(string_list(check, "stderr_needles"))
        stderr_absent = set(string_list(check, "stderr_absent_needles"))
        stderr_counts = string_counts(check, "stderr_counts")

        route_needles = stderr_needles & {BAND_ROUTE, FALLBACK_ROUTE}
        if len(route_needles) != 1:
            raise AssertionError(f"{name}: must require exactly one accepted validation route")
        route = next(iter(route_needles))
        if stderr_counts.get(route) != 1:
            raise AssertionError(f"{name}: must require exactly one final route report")
        if "[alarm]" not in stderr_absent:
            raise AssertionError(f"{name}: must reject alarms")
        if route == BAND_ROUTE:
            band_checks.append(check)
            if not name.endswith("-band"):
                raise AssertionError(f"{name}: band-route case name must end in -band")
            if "fallback" not in stderr_absent:
                raise AssertionError(f"{name}: must reject every fallback report")
        else:
            fallback_checks.append(check)
            if not name.endswith("-general-fallback"):
                raise AssertionError(f"{name}: fallback case name must state general-fallback")
            if "route=permutable-band" not in stderr_absent:
                raise AssertionError(f"{name}: must reject the band route")
            if "differs_from_args" not in check:
                raise AssertionError(
                    f"{name}: fallback must demonstrate a nontrivial result against a baseline"
                )
            string_list(check, "differs_from_args")

        is_diamond = "--diamond-tile" in args or "--full-diamond-tile" in args
        if is_diamond:
            if "32 *" not in needles:
                raise AssertionError(f"{name}: missing a tiled-loop marker")
            baseline_args = string_list(check, "differs_from_args")
            if not baseline_args:
                raise AssertionError(f"{name}: diamond second-level output lacks a baseline comparison")
            if "--second-level-tile" in baseline_args:
                raise AssertionError(
                    f"{name}: diamond baseline must remove --second-level-tile"
                )
        else:
            missing_markers = NESTED_TILE_MARKERS - needles
            if missing_markers:
                raise AssertionError(f"{name}: missing nested tile markers {sorted(missing_markers)}")
        if ("--parallel" in args or "--parallel-current" in args) and "parallel for" not in " ".join(needles):
            raise AssertionError(f"{name}: parallel variant lacks a parallel loop assertion")
        if "--multipar" in args:
            required_parallel = 1 if "--parallel-strict" in args else 2
            if string_counts(check, "stdout_min_counts").get("parallel for", 0) < required_parallel:
                raise AssertionError(
                    f"{name}: multipar variant must require at least "
                    f"{required_parallel} parallel loop(s)"
                )
        if ("--vector" in args or "--vector-current" in args) and "vector for" not in " ".join(needles):
            skipped = (
                "[vector-validation] status=skipped "
                "reason=hint-not-certifiable-or-non-innermost"
            )
            if skipped not in stderr_needles or "vector for" not in set(
                string_list(check, "absent_needles")
            ):
                raise AssertionError(
                    f"{name}: vector variant must assert either an applied loop "
                    "or an explicit checked skip"
                )
    by_non_iss_signature = {
        (tuple(arg for arg in string_list(check, "args") if arg != "--iss"), check.get("fixture"))
        for check in tiling_checks
        if "--iss" in string_list(check, "args")
    }
    for check in tiling_checks:
        args = string_list(check, "args")
        if "--iss" in args or check.get("name") == FALLBACK_CHECK:
            continue
        signature = (tuple(args), check.get("fixture"))
        if signature not in by_non_iss_signature:
            raise AssertionError(f"{check['name']}: missing matching ISS variant")

    route_by_name = {
        str(check["name"]): (
            BAND_ROUTE if check in band_checks else FALLBACK_ROUTE
        )
        for check in band_checks + fallback_checks
    }
    expected_routes = {
        **{name: BAND_ROUTE for name in REQUIRED_BAND_ROUTES},
        **{name: FALLBACK_ROUTE for name in REQUIRED_FALLBACK_ROUTES},
    }
    for name, route in expected_routes.items():
        if route_by_name.get(name) != route:
            raise AssertionError(f"{name}: missing required route {route!r}")
    missing_negatives = REQUIRED_NEGATIVES - set(names)
    if missing_negatives:
        raise AssertionError(f"missing required negative cases: {sorted(missing_negatives)!r}")

    mismatch = next(
        (check for check in checks if check.get("name") == "second-level-openscop-source-witness-mismatch"),
        None,
    )
    if mismatch is None:
        raise AssertionError("missing OpenScop source/witness mismatch negative")
    if mismatch.get("expect") != "failure" or mismatch.get("needle") != "parameter mismatch":
        raise AssertionError("OpenScop mismatch test must fail specifically at source-shape checking")
    if len(string_list(mismatch, "input_fixtures")) != 2:
        raise AssertionError("OpenScop mismatch test must supply both source and witness inputs")

    fallback = next(
        (check for check in checks if check.get("name") == FALLBACK_CHECK),
        None,
    )
    if fallback is None or fallback.get("expect") != "success":
        raise AssertionError("missing explicit successful general-fallback check")
    if "--second-level-tile" not in string_list(fallback, "args"):
        raise AssertionError("general fallback check must exercise second-level tiling")
    if not NESTED_TILE_MARKERS.issubset(set(string_list(fallback, "needles"))):
        raise AssertionError("general fallback check does not assert nested second-level tiling")
    if FALLBACK_ROUTE not in string_list(fallback, "stderr_needles"):
        raise AssertionError("general fallback check does not require the fallback route label")
    if string_counts(fallback, "stderr_counts").get(FALLBACK_ROUTE) != 1:
        raise AssertionError("general fallback check must require exactly one route report")
    if BAND_ROUTE in string_list(fallback, "stderr_needles"):
        raise AssertionError("general fallback check also accepts the permutable-band route")
    if "route=permutable-band" not in string_list(fallback, "stderr_absent_needles"):
        raise AssertionError("general fallback check does not reject the band route")


def main() -> None:
    path = Path(__file__).resolve().with_name("suite_manifest.json")
    check_manifest(path)
    data = json.loads(path.read_text(encoding="utf-8"))
    successful = [
        check for check in data["checks"]
        if check.get("expect") == "success" and "--second-level-tile" in check.get("args", [])
    ]
    band_count = sum(BAND_ROUTE in check.get("stderr_needles", []) for check in successful)
    fallback_count = sum(FALLBACK_ROUTE in check.get("stderr_needles", []) for check in successful)
    print(
        "second-level suite manifest: PASS "
        f"({band_count} band accepted, {fallback_count} explicit fallbacks)"
    )


if __name__ == "__main__":
    main()
