#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

SCAN_DIRS = [
    "src",
    "driver",
    "polygen",
    "common",
    "cfrontend",
    "cparser",
    "lib",
    "VPL/coq",
]

TOP_LEVEL_ROUTES = [
    {
        "route": "default sequential optimizer",
        "cli": "polopt <file.loop>",
        "theorem_file": "driver/PolOptCorrect.v",
        "theorem_names": ["Opt_correct", "Opt_prepared_correct"],
    },
    {
        "route": "ISS optimizer",
        "cli": "polopt --iss <file.loop>",
        "theorem_file": "driver/PolOptCorrect.v",
        "theorem_names": ["Opt_with_iss_correct", "Opt_prepared_with_iss_correct"],
    },
    {
        "route": "checked parallel current",
        "cli": "polopt --parallel-current <dim> <file.loop>",
        "theorem_file": "driver/ParallelPolOptCorrect.v",
        "theorem_names": ["Opt_parallel_current_correct"],
    },
    {
        "route": "diamond phase-aligned validation",
        "cli": "polcert before.scop mid.scop posttile.scop after.scop",
        "theorem_file": "src/TilingBandScheduleValidator.v",
        "theorem_names": ["band-aware tiling validator lemmas"],
        "note": "Executable four-phase route still needs a top-level composed theorem wrapper.",
    },
]


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    text: str


def iter_coq_files() -> list[Path]:
    files: list[Path] = []
    for rel in SCAN_DIRS:
        root = ROOT / rel
        if not root.exists():
            continue
        files.extend(sorted(root.rglob("*.v")))
    return files


def scan_pattern(pattern: re.Pattern[str], files: list[Path]) -> list[Finding]:
    findings: list[Finding] = []
    for path in files:
        rel = path.relative_to(ROOT)
        try:
            lines = path.read_text(errors="replace").splitlines()
        except OSError:
            continue
        for idx, line in enumerate(lines, start=1):
            if pattern.search(line):
                findings.append(Finding(str(rel), idx, line.strip()))
    return findings


def theorem_index(files: list[Path]) -> dict[str, list[str]]:
    pattern = re.compile(r"^\s*(Theorem|Lemma|Corollary|Proposition)\s+([A-Za-z0-9_']+)")
    index: dict[str, list[str]] = {}
    for path in files:
        rel = str(path.relative_to(ROOT))
        names: list[str] = []
        try:
            lines = path.read_text(errors="replace").splitlines()
        except OSError:
            continue
        for line in lines:
            match = pattern.match(line)
            if match:
                names.append(match.group(2))
        if names:
            index[rel] = names
    return index


def build_report() -> dict[str, object]:
    files = iter_coq_files()
    admitted = scan_pattern(re.compile(r"\b(admit|Admitted|ADMITTED)\b"), files)
    aborted = scan_pattern(re.compile(r"\bAbort\."), files)
    extraction_axioms = []
    extraction_dir = ROOT / "extraction"
    if extraction_dir.exists():
        for path in sorted(extraction_dir.glob("*.ml")):
            for idx, line in enumerate(path.read_text(errors="replace").splitlines(), start=1):
                if "AXIOM TO BE REALIZED" in line:
                    extraction_axioms.append(Finding(str(path.relative_to(ROOT)), idx, line.strip()))

    return {
        "root": str(ROOT),
        "scanned_dirs": SCAN_DIRS,
        "coq_file_count": len(files),
        "admitted_count": len(admitted),
        "abort_count": len(aborted),
        "extraction_axiom_count": len(extraction_axioms),
        "admitted": [asdict(item) for item in admitted],
        "aborted": [asdict(item) for item in aborted],
        "extraction_axioms": [asdict(item) for item in extraction_axioms],
        "top_level_routes": TOP_LEVEL_ROUTES,
        "theorem_index": theorem_index(files),
    }


def write_markdown(report: dict[str, object]) -> str:
    lines = [
        "# PolCert Proof Report",
        "",
        f"- Coq files scanned: `{report['coq_file_count']}`",
        f"- Local admitted markers: `{report['admitted_count']}`",
        f"- Local abort markers: `{report['abort_count']}`",
        f"- Extracted OCaml unrealized axioms: `{report['extraction_axiom_count']}`",
        "",
        "## Route Map",
        "",
        "| Route | CLI | Theorem file | Theorem names | Note |",
        "|---|---|---|---|---|",
    ]
    for route in report["top_level_routes"]:  # type: ignore[index]
        item = route
        names = ", ".join(item.get("theorem_names", []))
        note = item.get("note", "")
        lines.append(
            f"| {item['route']} | `{item['cli']}` | `{item['theorem_file']}` | {names} | {note} |"
        )

    if report["admitted_count"] or report["abort_count"]:  # type: ignore[index]
        lines.extend(["", "## Open Proof Markers", ""])
        for key in ("admitted", "aborted"):
            for item in report[key]:  # type: ignore[index]
                lines.append(f"- `{item['path']}:{item['line']}`: `{item['text']}`")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json-out")
    ap.add_argument("--markdown-out")
    args = ap.parse_args()

    report = build_report()
    if args.json_out:
        out = Path(args.json_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2, sort_keys=True))
    if args.markdown_out:
        out = Path(args.markdown_out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(write_markdown(report))
    if not args.json_out and not args.markdown_out:
        print(write_markdown(report), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
