#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "polopt_flag_suites"))

from manifest_runner import run_manifest_suite


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--polopt", default="./polopt")
    ap.add_argument(
        "--manifest",
        default=str(pathlib.Path(__file__).resolve().with_name("suite_manifest.json")),
    )
    args = ap.parse_args()

    return run_manifest_suite(
        manifest_path=pathlib.Path(args.manifest).resolve(),
        polopt=pathlib.Path(args.polopt).resolve(),
    )


if __name__ == "__main__":
    raise SystemExit(main())
