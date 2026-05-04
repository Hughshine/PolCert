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
    Capability("--second-level-tile", "supported", "sequential checked second-level tiling route", "second-level suite", "extend composition tests"),
    Capability("--parallel", "supported-component-verified", "Pluto-hinted route uses extracted tiling/parallel validators and codegen, but hint selection is still an OCaml wrapper", "pluto-compat parallel; parallel tests", "add a top-level Coq route for the Pluto hint oracle or keep --parallel-current as theorem-facing entry"),
    Capability("--parallel-current d", "supported", "explicit checked parallel dimension", "parallel-current suite", "keep separate from Pluto compatibility"),
    Capability("--diamond-tile", "supported-narrow", "extracted sequential non-ISS single-level four-phase diamond route", "diamond suite; Opt_diamond_band_correct", "extend rejected compositions"),
    Capability("--full-diamond-tile", "supported-narrow", "stronger producer mode over the same extracted checked diamond route", "pluto-compat full-diamond; Opt_diamond_band_correct", "add more full-diamond cases"),
]

DIAMOND_COMBINATIONS = [
    Capability("--diamond-tile --iss", "composition-gap", "ISS changes statement structure before diamond witness recovery", "tested rejection", "compose ISS witness with diamond phase witness"),
    Capability("--diamond-tile --parallel", "composition-gap", "current diamond route forces sequential noparallel scheduling", "tested rejection", "validate diamond first, then certify parallel target"),
    Capability("--diamond-tile --parallel-current d", "composition-gap", "explicit current dimension has not been composed with diamond current space", "route rejection", "run diamond phase validation before parallel-current checker"),
    Capability("--diamond-tile --second-level-tile", "composition-gap", "current diamond checker handles one tiling boundary", "tested rejection", "validate multiple tiling boundaries or add multi-level witness"),
    Capability("--diamond-tile --notile", "correct-rejection", "diamond requires a tiling phase", "route rejection", "keep rejecting"),
    Capability("--diamond-tile --identity", "correct-rejection", "diamond requires Pluto scheduling/skew plus tiling", "route rejection", "keep rejecting unless a meaningful identity-diamond route is designed"),
]


def table_rows() -> list[Capability]:
    rows: list[Capability] = []
    rows.extend(SUPPORTED)
    rows.extend(DIAMOND_COMBINATIONS)

    for flag, reason in sorted(compat.FRONTEND_OPTIONS.items()):
        rows.append(Capability(flag, "out-of-optimizer-surface", reason, "native compat rejection", "keep as separate importer/debug mode if needed"))
    for flag, reason in sorted(compat.CODEGEN_OPTIONS.items()):
        rows.append(Capability(flag, "validator-or-codegen-gap", reason, "native compat rejection", "implement checked PolOpt equivalent, not Pluto pass-through"))
    for flag, reason in sorted(compat.DFP_OPTIONS.items()):
        rows.append(Capability(flag, "surface-or-build-gap", reason, "native compat rejection", "enable solver build and validate produced affine schedules"))
    for flag, reason in sorted(compat.UNSUPPORTED_OPTIMIZER_OPTIONS.items()):
        rows.append(Capability(flag, "surface-gap", reason, "native compat rejection", "pass through as oracle tuning only after regression coverage"))
    for flag, reason in sorted(compat.DEPENDENCE_SOLVER_OPTIONS.items()):
        rows.append(Capability(flag, "surface-gap", reason, "native compat rejection", "pass through as oracle tuning, then validate output schedules"))
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
            "diamond_supported_route": "sequential non-ISS single-level four-phase route",
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
    lines.extend(["", "## Compatibility Checks", "", "| Check | Expectation | Fixture | Args |", "|---|---|---|---|"])
    for row in matrix["compatibility_checks"]:  # type: ignore[index]
        args = " ".join(row["args"])
        lines.append(f"| `{row['name']}` | {row['expect']} | `{row['fixture']}` | `{args}` |")
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
