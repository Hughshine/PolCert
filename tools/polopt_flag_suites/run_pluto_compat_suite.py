#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"


@dataclass(frozen=True)
class Check:
    name: str
    args: list[str]
    fixture: Path
    success: bool
    needle: str
    normalized: str | None = None
    effect_needles: tuple[str, ...] = ()
    effect_absent: tuple[str, ...] = ()
    differs_from_args: tuple[tuple[str, ...], ...] = ()


FLAGS = ["--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--nounrolljam", "--rar"]
MATMUL_NOTILE = ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
MATMUL_TILED = [*FLAGS, "--nodiamond-tile", "--noparallel"]
JACOBI_NODIAMOND = [*FLAGS, "--nodiamond-tile", "--noparallel"]
JACOBI_NODIAMOND_ISS = [*FLAGS, "--nodiamond-tile", "--noparallel", "--iss"]
JACOBI_DIAMOND = [*FLAGS, "--diamond-tile", "--noparallel"]
JACOBI_DIAMOND_ISS = [*FLAGS, "--diamond-tile", "--noparallel", "--iss"]
JACOBI_FULL_DIAMOND = [*FLAGS, "--full-diamond-tile", "--noparallel"]
JACOBI_FULL_DIAMOND_ISS = [*FLAGS, "--full-diamond-tile", "--noparallel", "--iss"]
MATMUL = ROOT / "tests" / "polopt-generated" / "inputs" / "matmul.loop"
JACOBI_1D = ROOT / "tests" / "polopt-generated" / "inputs" / "jacobi-1d-imper.loop"
MATMUL_INIT = ROOT / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"
DIAMOND_PARALLEL_BATCH = ROOT / "tools" / "parallel_current" / "fixtures" / "diamond-example-inner-batch.loop"
JACOBI_BATCH = ROOT / "tools" / "parallel_current" / "fixtures" / "jacobi-batch.loop"


CHECKS = [
    Check(
        "ordinary-tiled",
        MATMUL_TILED,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: <default>",
        effect_needles=("32 *", "/ 32"),
        differs_from_args=(tuple(MATMUL_NOTILE),),
    ),
    Check(
        "affine-only",
        MATMUL_NOTILE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --notile",
        effect_absent=("32 *", "/ 32"),
    ),
    Check("identity-notile", ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, True, "== Optimized Loop ==", "polopt args: --identity"),
    Check(
        "second-level",
        [*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"],
        MATMUL_INIT,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile",
        effect_absent=("32 *", "/ 32"),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "parallel",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --parallel",
        effect_needles=("parallel for",),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "diamond",
        JACOBI_DIAMOND,
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile",
        effect_needles=("% 4", "32 *"),
        differs_from_args=(tuple(JACOBI_NODIAMOND),),
    ),
    Check(
        "diamond-iss",
        JACOBI_DIAMOND_ISS,
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --diamond-tile",
        effect_needles=("% 4", "32 *"),
        differs_from_args=(tuple(JACOBI_NODIAMOND_ISS),),
    ),
    Check(
        "diamond-parallel",
        [*FLAGS, "--diamond-tile", "--parallel"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --parallel",
        effect_needles=("parallel for", "32 *", "/ 32", "i4 + (-1 * i5)"),
        differs_from_args=(tuple(JACOBI_DIAMOND),),
    ),
    Check(
        "diamond-iss-parallel",
        [*FLAGS, "--diamond-tile", "--parallel", "--iss"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --diamond-tile --parallel",
        effect_needles=("parallel for", "32 *", "/ 32", "i4 + (-1 * i5)"),
        differs_from_args=(tuple(JACOBI_DIAMOND_ISS),),
    ),
    Check(
        "diamond-parallel-jacobi-batch",
        [*FLAGS, "--diamond-tile", "--parallel"],
        JACOBI_BATCH,
        True,
        "== Optimized Loop ==",
        "polopt args: --diamond-tile --parallel",
        effect_needles=("parallel for", "64 *", "(-2 * i11)", "a[", "b["),
        differs_from_args=(tuple(JACOBI_DIAMOND),),
    ),
    Check(
        "diamond-second-level",
        [*FLAGS, "--diamond-tile", "--noparallel", "--second-level-tile"],
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --diamond-tile",
        effect_needles=("% 4",),
        differs_from_args=(tuple(JACOBI_NODIAMOND), tuple(JACOBI_DIAMOND)),
    ),
    Check(
        "diamond-iss-second-level",
        [*FLAGS, "--diamond-tile", "--noparallel", "--iss", "--second-level-tile"],
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile --diamond-tile",
        effect_needles=("% 4",),
        differs_from_args=(tuple(JACOBI_NODIAMOND_ISS), tuple(JACOBI_DIAMOND_ISS)),
    ),
    Check(
        "full-diamond",
        JACOBI_FULL_DIAMOND,
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --full-diamond-tile",
        effect_needles=("% 4", "32 *"),
        differs_from_args=(tuple(JACOBI_NODIAMOND),),
    ),
    Check(
        "full-diamond-iss",
        JACOBI_FULL_DIAMOND_ISS,
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --full-diamond-tile",
        effect_needles=("% 4", "32 *"),
        differs_from_args=(tuple(JACOBI_NODIAMOND_ISS),),
    ),
    Check(
        "full-diamond-second-level",
        [*FLAGS, "--full-diamond-tile", "--noparallel", "--second-level-tile"],
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --full-diamond-tile",
        effect_needles=("% 4",),
        differs_from_args=(tuple(JACOBI_NODIAMOND), tuple(JACOBI_FULL_DIAMOND)),
    ),
    Check(
        "full-diamond-iss-second-level",
        [*FLAGS, "--full-diamond-tile", "--noparallel", "--iss", "--second-level-tile"],
        JACOBI_1D,
        True,
        "== Optimized Loop ==",
        "polopt args: --iss --second-level-tile --full-diamond-tile",
        effect_needles=("% 4",),
        differs_from_args=(tuple(JACOBI_NODIAMOND_ISS), tuple(JACOBI_FULL_DIAMOND_ISS)),
    ),
    Check("reject-bare-default", [], MATMUL, False, "Pluto enables --intratileopt by default"),
    Check("reject-prevector", ["--tile", "--prevector", "--nodiamond-tile", "--noparallel"], MATMUL, False, "prevectorization is a Pluto codegen/post-transform effect"),
    Check("reject-unrolljam", ["--tile", "--unrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "unroll-jam is a Pluto post-codegen transform"),
    Check("reject-intratileopt", ["--tile", "--intratileopt", "--nodiamond-tile", "--noparallel"], MATMUL, False, "Pluto intra-tile schedule rewriting is not exposed"),
    Check("reject-pet", ["--pet", *FLAGS, "--nodiamond-tile", "--noparallel"], MATMUL, False, "frontend is polopt's verified loop extractor"),
    Check("reject-typedfuse", ["--tile", "--typedfuse", "--nodiamond-tile", "--noparallel"], MATMUL, False, "typed fusion depends on DFP"),
    Check("reject-bare-identity", ["--identity", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check("reject-identity-tile", ["--identity", "--tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check("reject-multipar", [*FLAGS, "--parallel", "--multipar", "--nodiamond-tile"], MATMUL, False, "multi-degree Pluto parallel extraction is not exposed"),
    Check("reject-tile-notile", [*FLAGS, "--tile", "--notile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--tile and --notile are both present"),
    Check("reject-diamond-nodiamond", [*FLAGS, "--diamond-tile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present"),
]


ROUTE_BINDINGS = {
    "seq_optimize_diamond = SBandTilingOpt.opt_diamond":
        "diamond route must use the extracted SBandTilingOpt.opt_diamond entry",
    "seq_optimize_diamond_iss = SBandTilingOpt.opt_diamond_with_iss":
        "diamond+ISS route must use the extracted SBandTilingOpt.opt_diamond_with_iss entry",
    "seq_optimize_identity = SPolOpt.opt_identity":
        "identity route must use the extracted SPolOpt.opt_identity entry",
    "seq_optimize_affine = SPolOpt.opt_affine":
        "affine route must use the extracted SPolOpt.opt_affine entry",
}


def check_route_bindings() -> list[str]:
    source = (ROOT / "syntax" / "SLoopMain.ml").read_text()
    failures = []
    for needle, reason in ROUTE_BINDINGS.items():
        if needle not in source:
            failures.append(f"route binding missing: {needle!r}; {reason}")
    return failures


def optimized_loop(output: str) -> str:
    marker = "== Optimized Loop =="
    pos = output.find(marker)
    if pos < 0:
        return output
    return output[pos:]


def run_polopt_compat(args: list[str], fixture: Path, timeout: int) -> subprocess.CompletedProcess[str]:
    cmd = [
        str(POLOPT),
        "--pluto-compat",
        "--explain",
        *args,
        str(fixture),
    ]
    return subprocess.run(cmd, cwd=str(ROOT), text=True, capture_output=True, timeout=timeout + 5, check=False)


def run_check(check: Check, timeout: int) -> str | None:
    try:
        proc = run_polopt_compat(check.args, check.fixture, timeout)
    except subprocess.TimeoutExpired:
        return f"{check.name}: native polopt compatibility mode timed out"
    output = proc.stdout + proc.stderr
    optimized = optimized_loop(output)
    if check.success:
        if proc.returncode != 0:
            return f"{check.name}: expected success, got exit {proc.returncode}\n{output}"
        if check.needle not in output:
            return f"{check.name}: missing {check.needle!r}\n{output}"
        if check.normalized is not None and check.normalized not in output:
            return f"{check.name}: missing normalized mapping {check.normalized!r}\n{output}"
        for needle in check.effect_needles:
            if needle not in optimized:
                return f"{check.name}: missing optimization effect marker {needle!r}\n{output}"
        for needle in check.effect_absent:
            if needle in optimized:
                return f"{check.name}: unexpected optimization marker {needle!r}\n{output}"
        for baseline_args in check.differs_from_args:
            try:
                baseline = run_polopt_compat(list(baseline_args), check.fixture, timeout)
            except subprocess.TimeoutExpired:
                return f"{check.name}: baseline comparison timed out for args {list(baseline_args)!r}"
            baseline_output = baseline.stdout + baseline.stderr
            if baseline.returncode != 0:
                return (
                    f"{check.name}: baseline comparison command failed with exit {baseline.returncode} "
                    f"for args {list(baseline_args)!r}\n{baseline_output}"
                )
            if optimized_loop(baseline_output) == optimized:
                return f"{check.name}: optimized loop did not differ from baseline args {list(baseline_args)!r}\n{output}"
    else:
        if proc.returncode == 0:
            return f"{check.name}: expected rejection, but command succeeded\n{output}"
        if check.needle not in output:
            return f"{check.name}: missing rejection reason {check.needle!r}\n{output}"
    return None


def main(argv: list[str]) -> int:
    timeout = 30
    if argv:
        if len(argv) == 2 and argv[0] == "--timeout":
            timeout = int(argv[1])
        else:
            print("Usage: run_pluto_compat_suite.py [--timeout SECONDS]", file=sys.stderr)
            return 2

    failures = check_route_bindings()
    if not POLOPT.exists():
        print(f"[pluto-compat-suite] missing polopt: {POLOPT}", file=sys.stderr)
        return 2
    missing = [check.fixture for check in CHECKS if not check.fixture.exists()]
    if missing:
        print("[pluto-compat-suite] missing fixtures:", file=sys.stderr)
        for path in missing:
            print(path, file=sys.stderr)
        return 2
    for check in CHECKS:
        failure = run_check(check, timeout)
        print(f"[pluto-compat-suite] {check.name}: {'PASS' if failure is None else 'FAIL'}")
        if failure is not None:
            failures.append(failure)

    if failures:
        print("[pluto-compat-suite] FAIL")
        for failure in failures:
            print(failure)
        return 1
    print(f"[pluto-compat-suite] OK ({len(CHECKS)} checks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
