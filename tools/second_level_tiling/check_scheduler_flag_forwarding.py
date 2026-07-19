#!/usr/bin/env python3
"""Static regression checks for second-level Pluto flag forwarding."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def definition_body(source: str, name: str) -> str:
    match = re.search(rf"^let {re.escape(name)}\b[^=]*=", source, re.MULTILINE)
    if match is None:
        raise AssertionError(f"missing Scheduler definition: {name}")
    next_definition = re.search(r"^let \w", source[match.end() :], re.MULTILINE)
    end = len(source) if next_definition is None else match.end() + next_definition.start()
    return source[match.end() : end]


def coq_definition_body(source: str, name: str) -> str:
    match = re.search(
        rf"^Definition {re.escape(name)}\b[\s\S]*?:=",
        source,
        re.MULTILINE,
    )
    if match is None:
        raise AssertionError(f"missing Coq definition: {name}")
    next_item = re.search(
        r"^(?:Definition|Lemma|Theorem|Inductive|Fixpoint)\s",
        source[match.end() :],
        re.MULTILINE,
    )
    end = len(source) if next_item is None else match.end() + next_item.start()
    return source[match.end() : end]


def require(body: str, needle: str, route: str) -> None:
    if needle not in body:
        raise AssertionError(f"{route} does not forward {needle}")


def require_count(body: str, needle: str, count: int, route: str) -> None:
    actual = body.count(needle)
    if actual != count:
        raise AssertionError(
            f"{route} contains {actual} occurrences of {needle}, expected {count}"
        )


def main() -> None:
    scheduler = (ROOT / "driver" / "Scheduler.ml").read_text(encoding="utf-8")

    for route in (
        "diamond_phase_flags",
        "diamond_phase_parallel_flags",
        "diamond_phase_vector_flags",
    ):
        require(
            definition_body(scheduler, route),
            "second_level_tiling_flags ()",
            route,
        )

    for route, base in (
        ("diamond_phase_with_iss_flags", "diamond_phase_flags ()"),
        (
            "diamond_phase_parallel_with_iss_flags",
            "diamond_phase_parallel_flags ()",
        ),
        ("diamond_phase_vector_with_iss_flags", "diamond_phase_vector_flags ()"),
    ):
        require(definition_body(scheduler, route), base, route)

    for route in (
        "tile_only_parallel_second_level_flags",
        "tile_only_vector_second_level_flags",
    ):
        require(definition_body(scheduler, route), '"--second-level-tile"', route)

    driver_config = (ROOT / "driver" / "VerifiedCompilerConfig.v").read_text(
        encoding="utf-8"
    )
    syntax_config = (ROOT / "syntax" / "SVerifiedCompilerConfig.v").read_text(
        encoding="utf-8"
    )
    for source, routes in (
        (
            driver_config,
            (
                "| VDefaultBand => BandCorrect.Opt_band loop",
                "| VSecondLevel => BandCorrect.Opt_band loop",
                "| VSecondLevelISS => BandCorrect.Opt_band_with_iss loop",
                "| VISS => BandCorrect.Opt_band_with_iss loop",
                "BandCorrect.Opt_identity_tiled_band loop",
                "BandCorrect.Opt_identity_tiled_band_with_iss loop",
                "| VDiamond => BandCorrect.Opt_diamond_band loop",
                "| VDiamondISS => BandCorrect.Opt_diamond_band_with_iss loop",
            ),
        ),
        (
            syntax_config,
            (
                "| VDefaultBand => SBandTilingOpt.opt loop",
                "| VSecondLevel => SBandTilingOpt.opt loop",
                "| VSecondLevelISS => SBandTilingOpt.opt_with_iss loop",
                "| VISS => SBandTilingOpt.opt_with_iss loop",
                "SBandTilingOpt.opt_identity_tiled loop",
                "SBandTilingOpt.opt_identity_tiled_with_iss loop",
                "| VDiamond => SBandTilingOpt.opt_diamond loop",
                "| VDiamondISS => SBandTilingOpt.opt_diamond_with_iss loop",
            ),
        ),
    ):
        for route in routes:
            require(source, route, "verified second-level config")

    unified_route = (
        "checked_tiling_schedule_sourceb_first_runtime_validate_route"
    )
    unified_correct = f"{unified_route}_correct"
    main_source = (ROOT / "syntax" / "SLoopMain.ml").read_text(encoding="utf-8")
    band_source = (ROOT / "src" / "TilingBandScheduleValidator.v").read_text(
        encoding="utf-8"
    )
    band_dispatcher = coq_definition_body(
        band_source, "checked_tiling_sourceb_first_band_check"
    )
    band_checks = (
        "check_pprog_pluto_permutable_tiling_bands_primary",
        "check_pprog_ordinary_tiling_permutability_via_validate_tiling",
        "check_pprog_second_level_permutable_bands_via_validate_tiling",
    )
    positions = [band_dispatcher.find(needle) for needle in band_checks]
    if any(position < 0 for position in positions) or positions != sorted(positions):
        raise AssertionError(
            "tiling dispatcher must try ordinary common-band, ordinary "
            "whole-program permutability, then second-level band"
        )
    ordinary_direct = coq_definition_body(
        band_source,
        "check_pprog_ordinary_tiling_permutability_via_validate_tiling",
    )
    ordinary_checks = (
        "check_ordinary_tiling_witnessesb",
        "check_pprog_permutable_tiling_bands_via_validate_tiling",
    )
    positions = [ordinary_direct.find(needle) for needle in ordinary_checks]
    if any(position < 0 for position in positions) or positions != sorted(positions):
        raise AssertionError(
            "whole-program ordinary tiling mode must be guarded by the "
            "ordinary-witness classifier"
        )
    fallback_dispatcher = coq_definition_body(band_source, unified_route)
    fallback_checks = (
        "checked_tiling_sourceb_first_band_check",
        "Canonical.checked_tiling_schedule_canonical_validate",
        "Base.checked_tiling_validate",
    )
    positions = [fallback_dispatcher.find(needle) for needle in fallback_checks]
    if any(position < 0 for position in positions) or positions != sorted(positions):
        raise AssertionError(
            "runtime tiling dispatcher must try band checks, canonical fallback, "
            "then general fallback"
        )

    for path, prefix in (
        (ROOT / "driver" / "VerifiedParallelCompilerConfig.v", "ParallelCore.Opt_"),
        (ROOT / "syntax" / "SVerifiedParallelCompilerConfig.v", "SParallelPolOpt.opt_"),
    ):
        source = path.read_text(encoding="utf-8")
        for suffix in (
            "parallel_current_identity_tiled loop d",
            "parallel_current_identity_tiled_with_iss loop d",
            "parallel_current loop d",
            "parallel_current_with_iss loop d",
            "parallel_current_diamond loop d",
            "parallel_current_diamond_with_iss loop d",
            "parallel_current_many_identity_tiled loop dims",
            "parallel_current_many_identity_tiled_with_iss loop dims",
            "parallel_current_many loop dims",
            "parallel_current_many_with_iss loop dims",
            "parallel_current_many_diamond loop dims",
            "parallel_current_many_diamond_with_iss loop dims",
            "vector_current_identity loop d",
            "vector_current_identity_tiled loop d",
            "vector_current_identity_tiled_with_iss loop d",
            "vector_current_affine loop d",
            "vector_current loop d",
            "vector_current_diamond loop d",
            "vector_current_diamond_with_iss loop d",
            "vector_current_identity_with_iss loop d",
            "vector_current_affine_with_iss loop d",
            "vector_current_with_iss loop d",
        ):
            require(
                source,
                prefix + suffix,
                f"tiling-bearing parallel config in {path.relative_to(ROOT)}",
            )

    sequential_config_body = definition_body(
        main_source, "verified_sequential_config_of_cli"
    )
    if "force_legacy_generic_tiling" in sequential_config_body:
        raise AssertionError("legacy compatibility flag must not bypass band-first dispatch")
    if re.search(r"\bRawDefault\b", sequential_config_body):
        raise AssertionError("the generic-primary RawDefault route must not be CLI-selectable")
    require(sequential_config_body, "RawDefaultBand", "normal default band route")
    for path, old_route, band_route in (
        (
            ROOT / "driver" / "VerifiedCompilerConfig.v",
            "VDefault => CoreCorrect.Core.Opt loop",
            "VDefault => BandCorrect.Opt_band loop",
        ),
        (
            ROOT / "syntax" / "SVerifiedCompilerConfig.v",
            "VDefault => SPolOpt.opt loop",
            "VDefault => SBandTilingOpt.opt loop",
        ),
    ):
        source = path.read_text(encoding="utf-8")
        if old_route in source:
            raise AssertionError(
                f"RawDefault in {path.relative_to(ROOT)} bypasses band-first dispatch"
            )
        require(
            source,
            band_route,
            f"RawDefault band-first dispatch in {path.relative_to(ROOT)}",
        )
    for path in (
        ROOT / "src" / "TilingBandScheduleValidator.v",
        ROOT / "driver" / "PolOptBandTiling.v",
        ROOT / "driver" / "ParallelPolOpt.v",
        ROOT / "syntax" / "STilingBandSched.v",
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
        ROOT / "driver" / "Entry.ml",
        ROOT / "syntax" / "SLoopMain.ml",
    ):
        require(
            path.read_text(encoding="utf-8"),
            unified_route,
            f"unified sourceb-first route in {path.relative_to(ROOT)}",
        )

    for path in (
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
    ):
        source = path.read_text(encoding="utf-8")
        require(source, "Definition reject_tiling_then", "observable rejected route helper")
        require(
            source,
            "observe_tiling_validation_route TilingSched.TilingBandRejected",
            "rejected tiling telemetry",
        )

    for path in (
        ROOT / "src" / "TilingBandScheduleValidator.v",
        ROOT / "driver" / "PolOptBandTiling.v",
        ROOT / "driver" / "ParallelPolOptCorrect.v",
    ):
        require(
            path.read_text(encoding="utf-8"),
            unified_correct,
            f"unified sourceb-first proof in {path.relative_to(ROOT)}",
        )

    for path in (
        ROOT / "syntax" / "SBandTilingOpt.v",
        ROOT / "syntax" / "SParallelPolOpt.v",
    ):
        require(
            path.read_text(encoding="utf-8"),
            "observe_tiling_validation_route",
            f"exact runtime route observation in {path.relative_to(ROOT)}",
        )

    require(
        (ROOT / "extraction" / "extraction.v").read_text(encoding="utf-8"),
        "TilingValidationRoute.record_coq_label",
        "extracted route recorder",
    )
    require(
        main_source,
        "TilingValidationRoute.capture",
        "final-candidate route reporting",
    )

    for route in (
        "try_verified_parallel_current_compile",
        "try_verified_parallel_current_many_compile",
    ):
        require_count(
            definition_body(main_source, route),
            "TilingValidationRoute.report",
            0,
            f"unreported candidate probe {route}",
        )
    for route in (
        "run_selected_optimization",
        "run_selected_sequential_loop_optimization",
        "run_verified_hinted_parallel_optimization",
        "run_verified_hinted_multipar_parallel_optimization",
        "run_selected_vector_optimization",
        "run_selected_parallel_current_optimization",
        "run_selected_vector_current_optimization",
    ):
        require_count(
            definition_body(main_source, route),
            "TilingValidationRoute.report",
            1,
            f"single final-candidate report {route}",
        )

    standalone_body = definition_body(main_source, "run_tiling_validator")
    for needle in (
        "TilingValidationRoute.capture",
        "tiling_forward_scops",
        "TilingValidationRoute.report",
    ):
        require(standalone_body, needle, "standalone OpenScop tiling validator")

    suite_runner = (
        ROOT / "tools" / "second_level_tiling" / "run_second_level_tile_suite.py"
    ).read_text(encoding="utf-8")
    require(
        suite_runner,
        "check_standalone_formal_route(",
        "standalone formal-route dynamic regression",
    )
    require(
        suite_runner,
        "check_second_level_diamond_route_matrix(",
        "second-level diamond current/strict route matrix",
    )
    standalone_regression = (
        ROOT
        / "tools"
        / "second_level_tiling"
        / "check_standalone_formal_route.py"
    ).read_text(encoding="utf-8")
    for needle in (
        '"formal: PASS"',
        "AFFINE_PLUTO_FLAGS",
        "TILING_PLUTO_FLAGS",
        "expected_route=BAND_ROUTE",
        "expected_route=FALLBACK_ROUTE",
        "if route_lines != [expected_route]",
        '"--validate-tiling-openscop"',
    ):
        require(
            standalone_regression,
            needle,
            "standalone formal-route dynamic regression",
        )

    for route in (
        "RawParallelCurrentIdentityTiledISS",
        "RawParallelCurrentManyIdentityTiledISS",
        "RawVectorCurrentIdentityTiledISS",
    ):
        require(main_source, route, "identity-tiled ISS parallel/vector dispatch")

    for route in (
        "parallel_hint_dims_of_cli",
        "vector_hint_dims_of_cli",
    ):
        body = definition_body(main_source, route)
        require(body, "if cfg.force_iss then", route)
        require(body, "apply_iss_bridge_to_spol_or_fail", route)

    vector_config = definition_body(
        main_source, "verified_vector_current_config_of_cli"
    )
    for constructor in (
        "RawVectorCurrentIdentityTiledISS",
        "RawVectorCurrentDiamondISS",
        "RawVectorCurrentDefaultISS",
    ):
        require(vector_config, constructor, "proved vector config dispatch")
    for route in (
        "try_verified_vector_current_compile",
        "run_selected_vector_optimization",
    ):
        require(
            definition_body(main_source, route),
            "VerifiedParallelCompiler.compile" if route == "try_verified_vector_current_compile" else "try_verified_vector_current_compile",
            "proved vector config execution",
        )
    require(
        definition_body(main_source, "run_selected_vector_current_optimization"),
        "VerifiedParallelCompiler.compile",
        "fail-closed explicit vector-current execution",
    )

    print("second-level scheduler flag forwarding: PASS")


if __name__ == "__main__":
    main()
