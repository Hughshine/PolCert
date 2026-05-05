#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools" / "polopt_flag_suites"))

import pluto_compat_driver as compat  # noqa: E402
import run_pluto_compat_suite as compat_suite  # noqa: E402


@dataclass(frozen=True)
class Capability:
    request: str
    status: str
    reason: str
    evidence: str
    next_step: str


SUPPORTED = [
    Capability("default tiled route", "supported", "extracted checked affine plus ordinary/second-level tiling route", "strict suite; pluto-compat ordinary-tiled; PolOptBandTiling Opt_band_correct", "keep as baseline"),
    Capability("--notile", "supported", "extracted affine-only checked route", "pluto-compat affine-only; Affine_opt_prepared_correct", "keep"),
    Capability("--identity --notile", "supported", "extracted no-Pluto identity extraction/codegen route", "pluto-compat identity-notile; Identity_opt_prepared_correct", "keep"),
    Capability("--iss", "supported", "ISS split validation plus ordinary optimization route", "ISS suites", "add artifact-check summary"),
    Capability("--second-level-tile", "supported", "checked second-level tiling route, including explicit-current and Pluto-hinted parallel compositions", "second-level suite; pluto-compat second-level-parallel", "broaden fixtures"),
    Capability("--parallel", "supported-component-verified", "Pluto-hinted route uses extracted tiling/parallel validators and codegen, but hint selection is still an OCaml wrapper", "pluto-compat parallel; pluto-compat parallel-multipar; parallel tests", "add a top-level Coq route for the Pluto hint oracle or keep --parallel-current as theorem-facing entry"),
    Capability("--parallel-current d", "supported", "explicit checked parallel dimension", "parallel-current suite; Opt_parallel_current_correct", "keep separate from Pluto compatibility"),
    Capability("--diamond-tile", "supported-narrow", "extracted four-phase diamond route with sequential, ISS, second-level, parallel, and multipar compositions", "diamond suite; pluto-compat diamond combinations; Opt_diamond_band_correct", "broaden effect fixtures and polish raw-codegen fallback output"),
    Capability("--full-diamond-tile", "supported-narrow", "stronger producer mode over the same extracted checked diamond route", "pluto-compat full-diamond; Opt_diamond_band_correct", "add more full-diamond cases"),
    Capability("--diamond-tile --iss", "supported-narrow", "ISS bridge validation is composed before the single-level four-phase diamond route", "pluto-compat diamond-iss; Opt_diamond_band_with_iss_correct", "add broader ISS+diamond fixtures"),
    Capability("--full-diamond-tile --iss", "supported-narrow", "full-diamond producer mode over the same checked ISS+diamond route", "pluto-compat full-diamond-iss; Opt_diamond_band_with_iss_correct", "add broader ISS+full-diamond fixtures"),
    Capability("--diamond-tile --second-level-tile", "supported-narrow", "second-level Pluto diamond output is checked by the same diamond route with second-level witness extraction enabled", "pluto-compat diamond-second-level; Opt_diamond_band_correct", "add broader second-level diamond fixtures"),
    Capability("--diamond-tile --iss --second-level-tile", "supported-narrow", "ISS bridge validation composes with second-level diamond witness extraction", "pluto-compat diamond-iss-second-level; Opt_diamond_band_with_iss_correct", "add broader ISS+second-level diamond fixtures"),
    Capability("--diamond-tile --parallel", "supported-narrow", "Pluto supplies the parallel hint; polopt routes the selected dimension through the checked diamond parallel-current validator with raw-codegen fallback when cleanup would make traces non-affine", "pluto-compat diamond-parallel; pluto-compat diamond-parallel-jacobi-batch; Opt_parallel_current_diamond_correct", "polish singleton-loop cleanup output"),
    Capability("--diamond-tile --parallel --multipar", "supported-narrow", "the extracted diamond pipeline can feed a list of candidate current dimensions into the checked multi-cert parallel codegen route", "pluto-compat diamond-parallel-multipar; checked_annotated_codegen_many_correct_general", "broaden diamond multipar fixtures and add strict-mode checks"),
    Capability("--diamond-tile --iss --parallel", "supported-narrow", "ISS bridge validation composes with the Pluto-hinted diamond parallel-current route", "pluto-compat diamond-iss-parallel; Opt_parallel_current_diamond_with_iss_correct", "broaden ISS fixtures beyond the single-statement batch stencil"),
    Capability("--diamond-tile --parallel-current d", "supported-narrow", "diamond route validates the four-phase diamond boundary before explicit current-space parallel certification; positive support includes the single-statement batch stencil and batched two-statement Jacobi via checked raw-codegen fallback", "parallel-current diamond-current-combined-effect; parallel-current diamond-current-jacobi-batch-positive; Opt_parallel_current_diamond_correct", "polish singleton-loop cleanup output"),
    Capability("--candldep --scalpriv", "supported-conservative-oracle-tuning", "Candl scalar-privatization is passed to Pluto only with --candldep; PolOpt still validates the produced schedule under the original scalar storage semantics", "pluto-compat optimizer-candldep-scalpriv-affine; bare --scalpriv rejection", "add a checked scalar-private storage rewrite before accepting schedules that require privatization"),
]

DIAMOND_COMBINATIONS = [
    Capability("--diamond-tile --notile", "correct-rejection", "diamond requires a tiling phase", "route rejection", "keep rejecting"),
    Capability("--diamond-tile --identity", "correct-rejection", "diamond requires Pluto scheduling/skew plus tiling", "route rejection", "keep rejecting unless a meaningful identity-diamond route is designed"),
]


def table_rows() -> list[Capability]:
    rows: list[Capability] = []
    rows.extend(SUPPORTED)
    rows.extend(DIAMOND_COMBINATIONS)
    for flag, reason in sorted(compat.SUPPORTED_OPTIMIZER_OPTIONS.items()):
        rows.append(Capability(flag, "supported-oracle-tuning", reason, "pluto-compat optimizer tuning checks; existing affine/tiling validators re-check the produced schedule", "broaden fixtures for additional effect cases"))
    for flag, reason in sorted(compat.SUPPORTED_VALUE_OPTIONS.items()):
        rows.append(Capability(flag + " <n>", "supported-oracle-tuning", reason, "pluto-compat optimizer tuning checks; existing affine/tiling validators re-check the produced schedule", "broaden value/effect fixtures"))
    for flag, reason in sorted(compat.CONDITIONAL_LP_SOLVER_OPTIONS.items()):
        rows.append(Capability(flag, "supported-oracle-tuning-with-runtime-probe", reason, "pinned GLPK-enabled Pluto baseline accepts and validates representative affine cases; alternate Pluto binaries are rejected if they lack the advertised option", "broaden non-matmul effect fixtures"))

    for flag, reason in sorted(compat.FRONTEND_OPTIONS.items()):
        rows.append(Capability(flag, "out-of-optimizer-surface", reason, "native compat rejection", "keep as separate importer/debug mode if needed"))
    for flag, reason in sorted(compat.CODEGEN_OPTIONS.items()):
        rows.append(Capability(flag, "validator-or-codegen-gap", reason, "native compat rejection", "implement checked PolOpt equivalent, not Pluto pass-through"))
    for flag, reason in sorted(compat.DFP_OPTIONS.items()):
        rows.append(Capability(flag, "surface-or-build-gap", reason, "native compat rejection", "enable solver build and validate produced affine schedules"))
    for flag, reason in sorted(compat.UNSUPPORTED_OPTIMIZER_OPTIONS.items()):
        rows.append(Capability(flag, "surface-gap", reason, "native compat rejection", "pass through as oracle tuning only after regression coverage"))
    for flag, reason in sorted(compat.DEPENDENCE_SOLVER_OPTIONS.items()):
        rows.append(Capability(flag, "validator-or-semantic-gap", reason, "native compat rejection", "implement a checked PolOpt equivalent before pass-through"))
    for flag, reason in sorted(compat.STALE_OR_NON_PLUTO_OPTIONS.items()):
        rows.append(Capability(flag, "stale-or-non-pluto", reason, "native compat rejection", "do not expose as optimizer compatibility"))
    return rows


def check_rows() -> list[dict[str, object]]:
    rows = []
    for check in compat_suite.CHECKS:
        rows.append(
            {
                "name": check.name,
                "args": check.args,
                "expect": "success" if check.success else "reject",
                "needle": check.needle,
                "normalized": check.normalized,
                "effect_needles": list(check.effect_needles),
                "effect_absent": list(check.effect_absent),
                "differs_from_args": [list(args) for args in check.differs_from_args],
                "fixture": str(check.fixture.relative_to(ROOT)),
            }
        )
    return rows


def build_matrix() -> dict[str, object]:
    return {
        "root": str(ROOT),
        "capabilities": [asdict(row) for row in table_rows()],
        "compatibility_checks": check_rows(),
        "summary": {
            "capability_rows": len(table_rows()),
            "compatibility_checks": len(compat_suite.CHECKS),
            "diamond_supported_route": "sequential, parallel, multipar, ISS, and second-level four-phase routes",
            "pluto_style_entry": "./polopt --pluto-compat",
        },
    }


def write_markdown(matrix: dict[str, object]) -> str:
    lines = [
        "# Pluto/PolOpt Capability Matrix",
        "",
        "- Pluto-style filtered entry: `./polopt --pluto-compat`",
        "",
        "## Capability Surface",
        "",
        "| Request | Status | Reason | Evidence | Next step |",
        "|---|---|---|---|---|",
    ]
    for row in matrix["capabilities"]:  # type: ignore[index]
        lines.append(
            f"| `{row['request']}` | {row['status']} | {row['reason']} | {row['evidence']} | {row['next_step']} |"
        )
    lines.extend(["", "## Compatibility Checks", "", "| Check | Expectation | Fixture | Args | Effect oracle |", "|---|---|---|---|---|"])
    for row in matrix["compatibility_checks"]:  # type: ignore[index]
        args = " ".join(row["args"])
        effect_parts = []
        if row["effect_needles"]:
            effect_parts.append("requires " + ", ".join(f"`{needle}`" for needle in row["effect_needles"]))
        if row["effect_absent"]:
            effect_parts.append("forbids " + ", ".join(f"`{needle}`" for needle in row["effect_absent"]))
        if row["differs_from_args"]:
            effect_parts.append("differs from baseline")
        effect = "; ".join(effect_parts) if effect_parts else ""
        lines.append(f"| `{row['name']}` | {row['expect']} | `{row['fixture']}` | `{args}` | {effect} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json-out")
    ap.add_argument("--markdown-out")
    args = ap.parse_args()

    matrix = build_matrix()
    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(matrix, indent=2, sort_keys=True))
    if args.markdown_out:
        out = Path(args.markdown_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(write_markdown(matrix))
    if not args.json_out and not args.markdown_out:
        print(write_markdown(matrix), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
