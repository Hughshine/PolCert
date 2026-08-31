#!/usr/bin/env python3
"""Replace Pluto phase outputs with a valid nonpermutable tiling pair."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    args = sys.argv[1:]
    real_pluto = os.environ.get("POLCERT_REAL_PLUTO", "/pluto/tool/pluto")
    proc = subprocess.run([real_pluto, *args], check=False)
    if proc.returncode != 0:
        return proc.returncode

    inputs = [Path(arg).resolve() for arg in args if arg.endswith(".scop")]
    if not inputs:
        return 70

    source = inputs[-1]
    output = source.with_name(source.name + ".afterscheduling.scop")
    fixtures = Path(__file__).resolve().parent / "fixtures"
    replacement = (
        fixtures / "nonpermutable-band.posttile.scop"
        if "--tile" in args
        else fixtures / "nonpermutable-band.midtransform.scop"
    )
    shutil.copyfile(replacement, output)
    print(
        "[frozen-nonpermutable-pluto] "
        f"replaced {output.name} with {replacement.name}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
