#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import re
import sys


OPEN_PROOF_RE = re.compile(r"\b(?:admit|Admitted|ADMITTED)\b|\bAbort\s*\.")


def coq_code_only(text: str) -> str:
    """Blank comments and strings while preserving offsets and line numbers."""
    result = list(text)
    comment_depth = 0
    in_string = False
    index = 0
    while index < len(text):
        pair = text[index : index + 2]
        if comment_depth:
            if pair == "(*":
                result[index] = result[index + 1] = " "
                comment_depth += 1
                index += 2
                continue
            if pair == "*)":
                result[index] = result[index + 1] = " "
                comment_depth -= 1
                index += 2
                continue
            if text[index] != "\n":
                result[index] = " "
            index += 1
            continue

        if in_string:
            if pair == '""':
                result[index] = result[index + 1] = " "
                index += 2
                continue
            if text[index] == '"':
                result[index] = " "
                in_string = False
            elif text[index] != "\n":
                result[index] = " "
            index += 1
            continue

        if pair == "(*":
            result[index] = result[index + 1] = " "
            comment_depth = 1
            index += 2
            continue
        if text[index] == '"':
            result[index] = " "
            in_string = True
        index += 1
    return "".join(result)


def find_open_proofs(path: pathlib.Path) -> list[tuple[int, str]]:
    text = path.read_text(encoding="utf-8", errors="replace")
    code = coq_code_only(text)
    return [
        (code.count("\n", 0, match.start()) + 1, match.group(0))
        for match in OPEN_PROOF_RE.finditer(code)
    ]


def check_files(files: list[pathlib.Path]) -> int:
    missing = [path for path in files if not path.is_file()]
    if missing:
        for path in missing:
            print(f"[open-proof] ERROR missing={path}", file=sys.stderr)
        return 2

    findings: list[tuple[pathlib.Path, int, str]] = []
    for path in files:
        findings.extend((path, line, marker) for line, marker in find_open_proofs(path))

    if findings:
        print(
            f"[open-proof] FAIL expected=0 actual={len(findings)} files={len(files)} "
            "interpretation=unfinished proof commands must not enter the artifact",
            file=sys.stderr,
        )
        for path, line, marker in findings:
            print(f"{path}:{line}: unfinished proof command: {marker}", file=sys.stderr)
        return 1
    print(
        f"[open-proof] PASS expected=0 actual=0 files={len(files)} "
        "interpretation=compiled Coq sources contain no unfinished proof commands"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject unfinished Coq proof commands in compiled project files."
    )
    parser.add_argument("files", nargs="+", type=pathlib.Path)
    args = parser.parse_args()

    return check_files(args.files)


if __name__ == "__main__":
    raise SystemExit(main())
