#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import os
from dataclasses import dataclass
from pathlib import Path

import pluto_compat_driver as compat


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
FLAGS_INTRATILE = ["--tile", "--smartfuse", "--intratileopt", "--noprevector", "--nounrolljam", "--rar"]
MATMUL_NOTILE = ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
MATMUL_TILED = [*FLAGS, "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_INTRATILE = [*FLAGS_INTRATILE, "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE = [*FLAGS, "--determine-tile-size", "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE_CACHE = [*FLAGS, "--determine-tile-size", "--cache-size=32768", "--nodiamond-tile", "--noparallel"]
MATMUL_TILED_DETERMINE_DATA = [*FLAGS, "--determine-tile-size", "--data-element-size=16", "--nodiamond-tile", "--noparallel"]
FUSION_NOTILE_SMART = ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
FUSION_NOTILE_NOFUSE = ["--notile", "--nofuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
FUSION_NOTILE_MAXFUSE = ["--notile", "--maxfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
FUSION_NOTILE_NODEPBOUND = ["--notile", "--smartfuse", "--nodepbound", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_PER_CC = ["--notile", "--smartfuse", "--per-cc-obj", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_FLIC = ["--notile", "--smartfuse", "--flic", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_FAST_LIN = ["--notile", "--smartfuse", "--fast-lin-ind-check", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_LASTWRITER = ["--notile", "--smartfuse", "--lastwriter", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_NOLASTWRITER = ["--notile", "--smartfuse", "--nolastwriter", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_CANDLDEP = ["--notile", "--smartfuse", "--candldep", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_PIPSOLVE = ["--notile", "--smartfuse", "--pipsolve", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ISL_ACCESSWISE = ["--notile", "--smartfuse", "--isldepaccesswise", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ISL_STMTWISE = ["--notile", "--smartfuse", "--isldepstmtwise", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ISL_COALESCE = ["--notile", "--smartfuse", "--isldepcoalesce", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_COEFF_BOUND = ["--notile", "--smartfuse", "--coeff-bound=10", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_COEFF_BOUND_TIGHT = ["--notile", "--smartfuse", "--coeff-bound=1", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_FORCEPARALLEL = ["--notile", "--smartfuse", "--forceparallel=1", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_GLPK = ["--notile", "--smartfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_ILP = ["--notile", "--smartfuse", "--glpk", "--ilp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_LP = ["--notile", "--smartfuse", "--glpk", "--lp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_LPCOLOR = ["--notile", "--smartfuse", "--glpk", "--lpcolor", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_DFP = ["--notile", "--smartfuse", "--glpk", "--dfp", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_CLUSTERSCC = ["--notile", "--smartfuse", "--glpk", "--clusterscc", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_HYBRIDFUSE = ["--notile", "--smartfuse", "--glpk", "--hybridfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_DELAYEDCUT = ["--notile", "--smartfuse", "--glpk", "--dfp", "--delayedcut", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
TUNING_NOTILE_TYPEDFUSE = ["--notile", "--typedfuse", "--glpk", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"]
MATMUL_TILED_PARTIAL_LEVELS = [*FLAGS, "--ft=0", "--lt=1", "--nodiamond-tile", "--noparallel"]
JACOBI_NODIAMOND = [*FLAGS, "--nodiamond-tile", "--noparallel"]
JACOBI_NODIAMOND_ISS = [*FLAGS, "--nodiamond-tile", "--noparallel", "--iss"]
JACOBI_DIAMOND = [*FLAGS, "--diamond-tile", "--noparallel"]
JACOBI_DIAMOND_ISS = [*FLAGS, "--diamond-tile", "--noparallel", "--iss"]
JACOBI_FULL_DIAMOND = [*FLAGS, "--full-diamond-tile", "--noparallel"]
JACOBI_FULL_DIAMOND_ISS = [*FLAGS, "--full-diamond-tile", "--noparallel", "--iss"]
MATMUL = ROOT / "tests" / "polopt-generated" / "inputs" / "matmul.loop"
REG_MATMUL = ROOT / "tests" / "polopt-regression" / "inputs" / "matmul.loop"
FUSION1 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion1.loop"
FUSION2 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion2.loop"
FUSION6 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion6.loop"
FUSION10 = ROOT / "tests" / "polopt-regression" / "inputs" / "fusion10.loop"
PCA = ROOT / "tests" / "polopt-regression" / "inputs" / "pca.loop"
COSTFUNC = ROOT / "tests" / "polopt-regression" / "inputs" / "costfunc.loop"
JACOBI_1D = ROOT / "tests" / "polopt-generated" / "inputs" / "jacobi-1d-imper.loop"
NODEP = ROOT / "tests" / "polopt-regression" / "inputs" / "nodep.loop"
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
        "optimizer-intratileopt",
        MATMUL_TILED_INTRATILE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --intratileopt",
        effect_needles=("for i1 in range(0, ((M + 31) / 32))",),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "optimizer-determine-tile-size",
        MATMUL_TILED_DETERMINE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --determine-tile-size",
        effect_needles=("2048 *",),
        differs_from_args=(tuple(MATMUL_TILED),),
    ),
    Check(
        "optimizer-cache-size",
        MATMUL_TILED_DETERMINE_CACHE,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --determine-tile-size --cache-size=32768",
        effect_needles=("64 *",),
        differs_from_args=(tuple(MATMUL_TILED_DETERMINE),),
    ),
    Check(
        "optimizer-data-element-size",
        MATMUL_TILED_DETERMINE_DATA,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --determine-tile-size --data-element-size=16",
        effect_needles=("1024 *",),
        differs_from_args=(tuple(MATMUL_TILED_DETERMINE),),
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
    Check(
        "optimizer-nofuse-affine",
        FUSION_NOTILE_NOFUSE,
        FUSION1,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --nofuse",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-maxfuse-affine",
        FUSION_NOTILE_MAXFUSE,
        FUSION6,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --maxfuse",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-nodepbound-affine",
        FUSION_NOTILE_NODEPBOUND,
        FUSION2,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --nodepbound",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-per-cc-obj-affine",
        TUNING_NOTILE_PER_CC,
        PCA,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --per-cc-obj",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-flic-affine",
        TUNING_NOTILE_FLIC,
        COSTFUNC,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --flic",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-fast-lin-ind-check-affine",
        TUNING_NOTILE_FAST_LIN,
        COSTFUNC,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --fast-lin-ind-check",
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-lastwriter-affine",
        TUNING_NOTILE_LASTWRITER,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --lastwriter",
        effect_needles=("for i0 in range(0, M)",),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-nolastwriter-affine",
        TUNING_NOTILE_NOLASTWRITER,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --nolastwriter",
    ),
    Check(
        "optimizer-pipsolve-affine",
        TUNING_NOTILE_PIPSOLVE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --pipsolve",
    ),
    Check(
        "optimizer-isldepaccesswise-affine",
        TUNING_NOTILE_ISL_ACCESSWISE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --isldepaccesswise",
    ),
    Check(
        "optimizer-isldepstmtwise-affine",
        TUNING_NOTILE_ISL_STMTWISE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --isldepstmtwise",
    ),
    Check(
        "optimizer-isldepcoalesce-affine",
        TUNING_NOTILE_ISL_COALESCE,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --isldepcoalesce",
    ),
    Check(
        "optimizer-coeff-bound-affine",
        TUNING_NOTILE_COEFF_BOUND,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --coeff-bound=10",
    ),
    Check(
        "optimizer-coeff-bound-tight-effect",
        TUNING_NOTILE_COEFF_BOUND_TIGHT,
        FUSION10,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --coeff-bound=1",
        effect_needles=("A[((2 * i0) + 0)]", "B[((2 * 1) + 1)]"),
        differs_from_args=(tuple(FUSION_NOTILE_SMART),),
    ),
    Check(
        "optimizer-forceparallel-pass-through",
        TUNING_NOTILE_FORCEPARALLEL,
        REG_MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --forceparallel=1",
    ),
    Check("identity-notile", ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, True, "== Optimized Loop ==", "polopt args: --identity"),
    Check(
        "partial-tiling-levels",
        MATMUL_TILED_PARTIAL_LEVELS,
        MATMUL,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --ft=0 --lt=1",
    ),
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
        "parallel-multipar",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--innerpar"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --multipar",
        effect_needles=("parallel for i0", "parallel for i2"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar"]),),
    ),
    Check(
        "second-level-parallel",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "polopt args: --second-level-tile --parallel",
        effect_needles=("parallel for", "32 *"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"]),),
    ),
    Check(
        "second-level-parallel-multipar",
        [*FLAGS, "--nodiamond-tile", "--parallel", "--multipar", "--innerpar", "--second-level-tile"],
        NODEP,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --multipar",
        effect_needles=("parallel for i0", "parallel for i1"),
        differs_from_args=(tuple([*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar", "--second-level-tile"]),),
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
        "diamond-parallel-multipar",
        [*FLAGS, "--diamond-tile", "--parallel", "--multipar", "--innerpar"],
        DIAMOND_PARALLEL_BATCH,
        True,
        "== Optimized Loop ==",
        "pluto oracle flags: --smartfuse --multipar",
        effect_needles=("parallel for i0", "parallel for i5", "i4 + (-1 * i5)"),
        differs_from_args=(tuple([*FLAGS, "--diamond-tile", "--parallel", "--innerpar"]),),
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
    Check("reject-intratile-conflict", ["--tile", "--intratileopt", "--nointratileopt", "--nodiamond-tile", "--noparallel"], MATMUL, False, "contradictory tile-schedule controls"),
    Check("reject-lastwriter-conflict", ["--notile", "--lastwriter", "--nolastwriter", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "contradictory dependence controls"),
    Check("reject-ft-without-lt", [*FLAGS, "--ft=0", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--ft and --lt must be supplied together"),
    Check("reject-pet", ["--pet", *FLAGS, "--nodiamond-tile", "--noparallel"], MATMUL, False, "frontend is polopt's verified loop extractor"),
    Check("reject-typedfuse", ["--tile", "--typedfuse", "--nodiamond-tile", "--noparallel"], MATMUL, False, "requires a GLPK- or Gurobi-enabled Pluto binary"),
    Check("reject-scalpriv", ["--notile", "--scalpriv", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "scalar privatization is a Candl-only dependence-pruning mode"),
    Check("reject-cache-without-determine", [*FLAGS, "--cache-size=32768", "--nodiamond-tile", "--noparallel"], MATMUL, False, "require --determine-tile-size"),
    Check("reject-bare-identity", ["--identity", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check("reject-identity-tile", ["--identity", "--tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check("reject-tile-notile", [*FLAGS, "--tile", "--notile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--tile and --notile are both present"),
    Check("reject-diamond-nodiamond", [*FLAGS, "--diamond-tile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present"),
]


def pluto_help_text() -> str:
    pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
    try:
        proc = subprocess.run(
            [str(pluto), "--help"],
            text=True,
            capture_output=True,
            timeout=10,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    return proc.stdout + proc.stderr


def pluto_supports_option(flag: str) -> bool:
    return flag in pluto_help_text()


def pluto_has_lp_solver_support() -> bool:
    help_text = pluto_help_text()
    return "--glpk" in help_text or "--gurobi" in help_text


def active_checks() -> list[Check]:
    checks = list(CHECKS)
    if pluto_has_lp_solver_support():
        checks = [check for check in checks if check.name != "reject-typedfuse"]
        checks.extend(
            [
                Check(
                    "optimizer-glpk-affine",
                    TUNING_NOTILE_GLPK,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-ilp-affine",
                    TUNING_NOTILE_ILP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --ilp",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-lp-affine",
                    TUNING_NOTILE_LP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --lp",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-lpcolor-affine",
                    TUNING_NOTILE_LPCOLOR,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --lpcolor",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-dfp-affine",
                    TUNING_NOTILE_DFP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --dfp",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-clusterscc-affine",
                    TUNING_NOTILE_CLUSTERSCC,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --clusterscc",
                    effect_needles=("for i0 in range(0, M)", "A[i0][i2]"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-hybridfuse-affine",
                    TUNING_NOTILE_HYBRIDFUSE,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --hybridfuse",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-delayedcut-affine",
                    TUNING_NOTILE_DELAYEDCUT,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --glpk --dfp --delayedcut",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
                Check(
                    "optimizer-typedfuse-affine",
                    TUNING_NOTILE_TYPEDFUSE,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --typedfuse --glpk",
                    effect_needles=("for i1 in range(i0, (N + i0))", "(-1 * i0)"),
                    differs_from_args=(tuple(FUSION_NOTILE_SMART),),
                ),
            ]
        )
    else:
        checks.extend(
            [
                Check("reject-glpk-without-solver-build", ["--notile", "--glpk", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "does not advertise this LP/DFP option"),
                Check("reject-lp-without-solver-build", ["--notile", "--lp", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "does not advertise this LP/DFP option"),
            ]
        )
    if compat.pluto_has_working_candldep():
        checks.extend(
            [
                Check(
                    "optimizer-candldep-affine",
                    TUNING_NOTILE_CANDLDEP,
                    REG_MATMUL,
                    True,
                    "== Optimized Loop ==",
                    "pluto oracle flags: --smartfuse --candldep",
                ),
                Check(
                    "reject-candldep-lastwriter",
                    ["--notile", "--smartfuse", "--candldep", "--lastwriter", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
                    REG_MATMUL,
                    False,
                    "--lastwriter is only supported with Pluto's ISL dependence tester",
                ),
                Check(
                    "reject-isldep-candldep",
                    ["--notile", "--smartfuse", "--isldep", "--candldep", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
                    REG_MATMUL,
                    False,
                    "--isldep and --candldep are both present",
                ),
            ]
        )
    else:
        checks.append(
            Check(
                "reject-candldep-broken-importer",
                ["--notile", "--candldep", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"],
                MATMUL,
                False,
                "selected Pluto Candl importer aborts on a dependent probe",
            )
        )
    return checks


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
    checks = active_checks()
    missing = [check.fixture for check in checks if not check.fixture.exists()]
    if missing:
        print("[pluto-compat-suite] missing fixtures:", file=sys.stderr)
        for path in missing:
            print(path, file=sys.stderr)
        return 2
    for check in checks:
        failure = run_check(check, timeout)
        print(f"[pluto-compat-suite] {check.name}: {'PASS' if failure is None else 'FAIL'}")
        if failure is not None:
            failures.append(failure)

    if failures:
        print("[pluto-compat-suite] FAIL")
        for failure in failures:
            print(failure)
        return 1
    print(f"[pluto-compat-suite] OK ({len(checks)} checks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
