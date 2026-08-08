#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import sys


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "polopt_flag_suites"))

from manifest_runner import run_manifest_suite
from check_rejected_tiling_route import check_rejected_tiling_route
from check_second_level_diamond_routes import check_second_level_diamond_route_matrix
from check_suite_manifest import check_manifest
from check_standalone_formal_route import check_standalone_formal_route


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--polopt", default="./polopt")
    ap.add_argument(
        "--manifest",
        default=str(pathlib.Path(__file__).resolve().with_name("suite_manifest.json")),
    )
    ap.add_argument(
        "--part",
        choices=("all", "routes", "rejection", "manifest"),
        default="all",
        help="run one independently schedulable part of the suite",
    )
    ap.add_argument("--timeout", type=int, default=120)
    args = ap.parse_args()

    manifest_path = pathlib.Path(args.manifest).resolve()
    polopt = pathlib.Path(args.polopt).resolve()
    symbolic_fixture = (
        pathlib.Path(__file__).resolve().parent
        / "fixtures"
        / "symbolic-independent-2d.loop"
    )

    if args.part in ("all", "routes"):
        check_standalone_formal_route(
            polopt=polopt,
            loop_fixture=symbolic_fixture,
            timeout=args.timeout,
        )
        check_second_level_diamond_route_matrix(
            polopt=polopt,
            fixture=(
                pathlib.Path(__file__).resolve().parents[1]
                / "parallel_current"
                / "fixtures"
                / "diamond-example-inner-batch.loop"
            ),
            timeout=args.timeout,
        )

    if args.part in ("all", "rejection"):
        check_rejected_tiling_route(
            polopt=polopt,
            fixture=symbolic_fixture,
            timeout=args.timeout,
        )

    if args.part in ("all", "manifest"):
        check_manifest(manifest_path)
        return run_manifest_suite(
            manifest_path=manifest_path,
            polopt=polopt,
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
