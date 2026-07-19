#!/usr/bin/env python3
"""Test-only Pluto wrapper that corrupts one second-level tile-link pair."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys


def scheduled_output(args: list[str]) -> Path | None:
    inputs = [Path(arg).resolve() for arg in args if arg.endswith(".scop")]
    if not inputs:
        return None
    source = inputs[-1]
    candidates = (
        source.with_name(source.name + ".afterscheduling.scop"),
        Path.cwd() / (source.name + ".afterscheduling.scop"),
    )
    return next((path for path in candidates if path.is_file()), None)


def main() -> int:
    real_pluto = os.environ.get("POLCERT_REAL_PLUTO", "/pluto/tool/pluto")
    args = sys.argv[1:]
    proc = subprocess.run([real_pluto, *args], check=False)
    if proc.returncode != 0:
        return proc.returncode
    if "--second-level-tile" not in args or "--tile" not in args:
        return 0

    output = scheduled_output(args)
    if output is None:
        print("[rejecting-pluto] missing scheduled OpenScop output", file=sys.stderr)
        return 70
    lines = output.read_text(encoding="utf-8").splitlines(keepends=True)
    count = 0
    for index, line in enumerate(lines):
        if not line.lstrip().startswith("1 "):
            continue
        changed, replacements = re.subn(
            r"(?<!\d)-(256|32|8)(?!\d)",
            lambda match: str(-int(match.group(1)) + 1),
            line,
            count=1,
        )
        if replacements == 1:
            lines[index] = changed
            count = 1
            break
    if count != 1:
        print("[rejecting-pluto] no second-level tile-link row found", file=sys.stderr)
        return 71
    output.write_text("".join(lines), encoding="utf-8")
    print("[rejecting-pluto] corrupted one second-level tile-link", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
