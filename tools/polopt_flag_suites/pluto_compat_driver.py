#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_POLOPT = ROOT / "polopt"


class Reject(Exception):
    pass


@dataclass(frozen=True)
class WrapperConfig:
    polopt: Path
    dry_run: bool
    explain: bool
    timeout: float | None


@dataclass
class PlutoFlagState:
    input_path: Path
    tile: bool = True
    tile_seen: bool = False
    notile_seen: bool = False
    identity: bool = False
    iss: bool = False
    second_level_tile: bool = False
    diamond_tile: bool = False
    diamond_seen: bool = False
    nodiamond_seen: bool = False
    full_diamond_tile: bool = False
    parallel: bool = False
    parallel_seen: bool = False
    vector: bool = False
    prevector_seen: bool = False
    multipar: bool = False
    innerpar_seen: bool = False
    no_parallel_seen: bool = False
    isldep_seen: bool = False
    candldep_seen: bool = False
    intratileopt_seen: bool = False
    no_intratileopt_seen: bool = False
    no_prevector_seen: bool = False
    unrolljam_seen: bool = False
    no_unrolljam_seen: bool = False
    oracle_flags: list[str] | None = None
    control_files: list[tuple[str, str]] | None = None
    notes: list[str] | None = None

    def add_note(self, msg: str) -> None:
        if self.notes is None:
            self.notes = []
        self.notes.append(msg)

    def add_oracle_flag(self, flag: str) -> None:
        if self.oracle_flags is None:
            self.oracle_flags = []
        self.oracle_flags.append(flag)

    def add_control_file(self, flag: str, target: str, value: str) -> None:
        if not Path(value).exists():
            raise Reject(f"{flag}: no such file: {value}")
        if self.control_files is None:
            self.control_files = []
        self.control_files.append((flag, value))
        self.add_note(f"{flag} installs explicit Pluto {target} control input for the checked oracle run")


VALUE_OPTIONS = {
    "--cache-size",
    "--cloogf",
    "--cloogl",
    "--codegen-context",
    "--coeff-bound",
    "--data-element-size",
    "--forceparallel",
    "--fst-file",
    "--ft",
    "--fusion-structure",
    "--lt",
    "--precut",
    "--precut-file",
    "--tile-sizes-file",
    "--ufactor",
    "-o",
}

FRONTEND_OPTIONS = {
    "--pet": "frontend is polopt's verified loop extractor, not Pluto/PET",
    "--readscop": "frontend is polopt's verified loop extractor, not Pluto OpenScop input",
    "--dumpscop": "Pluto OpenScop dumps are an oracle-debug interface, not a polopt input/output mode",
}

META_OPTIONS = {
    "--help": "CLI help is outside the optimizer-compatibility surface",
    "--version": "CLI version reporting is outside the optimizer-compatibility surface",
}

DEPENDENCE_SOLVER_OPTIONS = {}

DFP_OPTIONS = {
}

CODEGEN_OPTIONS = {
    "--bee": "Bee pragmas are Pluto codegen output, while polopt uses its own codegen",
    "--cloogsh": "Cloog codegen tuning is outside the polopt checked route",
    "--indent": "formatting is outside the optimizer-validation route",
}

UNSUPPORTED_OPTIMIZER_OPTIONS = {}

SUPPORTED_OPTIMIZER_OPTIONS = {
    "--smartfuse": "Pluto smart fusion policy is passed to the checked scheduler oracle",
    "--nofuse": "Pluto no-fusion policy is passed to the checked scheduler oracle",
    "--maxfuse": "Pluto maximal-fusion policy is passed to the checked scheduler oracle",
    "--nodepbound": "Pluto dependence-bound search tuning is passed to the checked scheduler oracle",
    "--per-cc-obj": "Pluto per-connected-component objective is passed to the checked scheduler oracle",
    "--flic": "Pluto fast linear-independence search is passed to the checked scheduler oracle",
    "--fast-lin-ind-check": "Pluto fast linear-independence search is passed to the checked scheduler oracle",
    "--determine-tile-size": "Pluto automatic tile-size selection is passed to the checked scheduler oracle",
    "--candldep": "Pluto Candl dependence analysis is passed through when the selected Pluto binary passes the Candl importer smoke probe",
    "--lastwriter": "Pluto last-writer dependence mode is passed to the checked scheduler oracle",
    "--nolastwriter": "Pluto default transitive dependence mode is passed to the checked scheduler oracle",
    "--isldepaccesswise": "Pluto ISL access-wise dependence extraction is passed to the checked scheduler oracle",
    "--isldepstmtwise": "Pluto ISL statement-wise dependence extraction is passed to the checked scheduler oracle",
    "--isldepcoalesce": "Pluto ISL dependence coalescing is passed to the checked scheduler oracle",
    "--pipsolve": "Pluto PIP solver selection is passed to the checked scheduler oracle",
    "--intratileopt": "Pluto intra-tile schedule rewriting is passed to the checked scheduler oracle",
    "--multipar": "Pluto multi-degree parallel extraction is passed to the checked scheduler oracle",
}

SUPPORTED_VALUE_OPTIONS = {
    "--cache-size": "Pluto cache-size tile model parameter is passed to the checked scheduler oracle",
    "--coeff-bound": "Pluto affine coefficient bound is passed to the checked scheduler oracle",
    "--data-element-size": "Pluto data-element-size tile model parameter is passed to the checked scheduler oracle",
    "--forceparallel": "Pluto force-parallel bit-vector is passed through; this pinned Pluto source has no effective use site",
    "--ft": "Pluto first tiled hyperplane level is passed to the checked scheduler oracle",
    "--lt": "Pluto last tiled hyperplane level is passed to the checked scheduler oracle",
    "--ufactor": "Pluto tile-size model unroll factor is passed through with --determine-tile-size; with checked --unrolljam it is used by the verified LoopUnroll post pass",
}

NONNEGATIVE_VALUE_OPTIONS = {"--forceparallel", "--ft", "--lt"}

CONDITIONAL_LP_SOLVER_OPTIONS = {
    "--clusterscc": "Pluto DFP SCC clustering is passed through when the selected Pluto binary advertises LP/DFP support",
    "--delayedcut": "Pluto DFP delayed-cut mode is passed through when the selected Pluto binary has GLPK or Gurobi support",
    "--dfp": "Pluto DFP scheduler mode is passed through when the selected Pluto binary advertises LP/DFP support",
    "--glpk": "Pluto GLPK solver selection is passed through when the selected Pluto binary advertises --glpk",
    "--gurobi": "Pluto Gurobi solver selection is passed through when the selected Pluto binary advertises --gurobi",
    "--hybridfuse": "Pluto hybrid fusion is passed through when the selected Pluto binary has GLPK or Gurobi support",
    "--ilp": "Pluto DFP ILP mode is passed through when the selected Pluto binary advertises LP/DFP support",
    "--lp": "Pluto LP relaxation mode is passed through when the selected Pluto binary advertises --lp",
    "--lpcolor": "Pluto LP-coloring mode is passed through when the selected Pluto binary advertises LP/DFP support",
    "--typedfuse": "Pluto typed fusion is passed through when the selected Pluto binary has GLPK or Gurobi support",
}

LP_SOLVER_OPTIONS = set(CONDITIONAL_LP_SOLVER_OPTIONS)

LP_SOLVER_DEPENDENT_OPTIONS = {"--typedfuse", "--hybridfuse", "--delayedcut"}


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


PLUTO_HELP = pluto_help_text()


def pluto_supports_option(flag: str) -> bool:
    return flag in PLUTO_HELP


def pluto_has_lp_solver_support() -> bool:
    return pluto_supports_option("--glpk") or pluto_supports_option("--gurobi")


_PLUTO_CANDLDEP_WORKS: bool | None = None


def pluto_has_working_candldep() -> bool:
    global _PLUTO_CANDLDEP_WORKS
    if _PLUTO_CANDLDEP_WORKS is not None:
        return _PLUTO_CANDLDEP_WORKS

    pluto = Path(os.environ.get("POLCERT_PLUTO", "/pluto/tool/pluto"))
    source = (
        "void candl_probe(int N, int A[]) {\n"
        "int i;\n"
        "#pragma scop\n"
        "for (i = 1; i < N; i++) {\n"
        "  A[i] = A[i - 1] + 1;\n"
        "}\n"
        "#pragma endscop\n"
        "}\n"
    )
    with tempfile.TemporaryDirectory(prefix="polcert-candldep-probe-") as tmp:
        src = Path(tmp) / "probe.c"
        out = Path(tmp) / "out.c"
        src.write_text(source)
        try:
            proc = subprocess.run(
                [
                    str(pluto),
                    "--candldep",
                    "--notile",
                    "--noprevector",
                    "--nounrolljam",
                    "--nodiamond-tile",
                    "--noparallel",
                    "-o",
                    str(out),
                    str(src),
                ],
                text=True,
                capture_output=True,
                timeout=10,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired):
            _PLUTO_CANDLDEP_WORKS = False
            return False
    _PLUTO_CANDLDEP_WORKS = proc.returncode == 0
    return _PLUTO_CANDLDEP_WORKS

STALE_OR_NON_PLUTO_OPTIONS = {
    "--dump-iss-bridge": "this flag is not accepted by the current Pluto binary",
    "--lbtile": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
    "--multipipe": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
    "--output": "the current Pluto binary uses -o, not --output",
    "--sched": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
    "--variables_not_global": "this flag appears in stale scripts but is not accepted by the current Pluto binary",
}

ACCEPTED_NOOPS = {
    "--debug",
    "--islsolve",
    "--moredebug",
    "--nocloogbacktrack",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--rar",
    "--silent",
}


def usage() -> str:
    return (
        "Usage: pluto_compat_driver.py [--polopt PATH] [--dry-run] [--explain] "
        "[--timeout SECONDS] <pluto-like flags> <file.loop>"
    )


def parse_wrapper_args(argv: list[str]) -> tuple[WrapperConfig, list[str]]:
    polopt = DEFAULT_POLOPT
    dry_run = False
    explain = False
    timeout: float | None = None
    rest: list[str] = []
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--polopt":
            i += 1
            if i >= len(argv):
                raise Reject("--polopt requires a path")
            polopt = Path(argv[i])
        elif arg.startswith("--polopt="):
            polopt = Path(arg.split("=", 1)[1])
        elif arg == "--dry-run":
            dry_run = True
        elif arg == "--explain":
            explain = True
        elif arg == "--timeout":
            i += 1
            if i >= len(argv):
                raise Reject("--timeout requires seconds")
            timeout = float(argv[i])
        elif arg.startswith("--timeout="):
            timeout = float(arg.split("=", 1)[1])
        elif arg == "--":
            rest.extend(argv[i + 1 :])
            break
        else:
            rest.append(arg)
        i += 1

    return WrapperConfig(polopt=polopt, dry_run=dry_run, explain=explain, timeout=timeout), rest


def split_flags_and_input(args: list[str]) -> tuple[list[tuple[str, str | None]], Path]:
    if not args:
        raise Reject(usage())
    input_arg = args[-1]
    if input_arg.startswith("-"):
        raise Reject("missing input .loop file")
    raw_flags = args[:-1]
    flags: list[tuple[str, str | None]] = []
    i = 0
    while i < len(raw_flags):
        flag = raw_flags[i]
        if flag in VALUE_OPTIONS:
            i += 1
            if i >= len(raw_flags):
                raise Reject(f"{flag} requires a value")
            flags.append((flag, raw_flags[i]))
        elif any(flag.startswith(prefix + "=") for prefix in VALUE_OPTIONS):
            prefix, value = flag.split("=", 1)
            flags.append((prefix, value))
        else:
            flags.append((flag, None))
        i += 1
    return flags, Path(input_arg)


def reject_known_flag(flag: str) -> str | None:
    for table in (
        FRONTEND_OPTIONS,
        META_OPTIONS,
        DEPENDENCE_SOLVER_OPTIONS,
        DFP_OPTIONS,
        CODEGEN_OPTIONS,
        UNSUPPORTED_OPTIMIZER_OPTIONS,
        STALE_OR_NON_PLUTO_OPTIONS,
    ):
        if flag in table:
            return table[flag]
    return None


def normalize_pluto_flags(flags: list[tuple[str, str | None]], input_path: Path) -> PlutoFlagState:
    state = PlutoFlagState(input_path=input_path)
    for flag, value in flags:
        reason = reject_known_flag(flag)
        if reason is not None:
            raise Reject(f"{flag}: {reason}")

        if flag == "--tile":
            state.tile = True
            state.tile_seen = True
        elif flag == "--notile":
            state.tile = False
            state.notile_seen = True
        elif flag == "--identity":
            state.identity = True
        elif flag == "--iss":
            state.iss = True
        elif flag == "--second-level-tile":
            state.second_level_tile = True
        elif flag == "--diamond-tile":
            state.diamond_tile = True
            state.diamond_seen = True
        elif flag == "--nodiamond-tile":
            state.diamond_tile = False
            state.nodiamond_seen = True
            state.full_diamond_tile = False
        elif flag == "--full-diamond-tile":
            state.diamond_tile = True
            state.diamond_seen = True
            state.full_diamond_tile = True
        elif flag in ("--parallel", "--parallelize"):
            state.parallel = True
            state.parallel_seen = True
        elif flag == "--multipar":
            state.parallel = True
            state.parallel_seen = True
            state.multipar = True
            state.add_oracle_flag(flag)
            state.add_note("--multipar enables checked parallel dimensions when available")
        elif flag == "--noparallel":
            state.parallel = False
            state.no_parallel_seen = True
        elif flag == "--innerpar":
            state.innerpar_seen = True
            state.add_note("--innerpar is implicit in polopt's current --parallel route")
        elif flag == "--tile-sizes-file":
            assert value is not None
            state.add_control_file(flag, "tile.sizes", value)
        elif flag in ("--fusion-structure", "--fst-file"):
            assert value is not None
            state.add_control_file(flag, ".fst", value)
        elif flag in ("--precut", "--precut-file"):
            assert value is not None
            state.add_control_file(flag, ".precut", value)
        elif flag == "--nointratileopt":
            state.no_intratileopt_seen = True
            state.add_note("--nointratileopt accepted because checked routes disable Pluto intra-tile rewriting")
        elif flag == "--intratileopt":
            state.intratileopt_seen = True
            state.add_oracle_flag(flag)
            state.add_note(f"{flag} passed through to Pluto's checked scheduler oracle")
        elif flag == "--isldep":
            state.isldep_seen = True
            state.add_note("--isldep accepted as Pluto's default dependence tester for the checked polopt route")
        elif flag == "--candldep":
            if not pluto_has_working_candldep():
                raise Reject("--candldep: selected Pluto Candl importer aborts on a dependent probe; requires the Candl dependence-type import fix")
            state.candldep_seen = True
            state.add_oracle_flag(flag)
            state.add_note(f"{flag} passed through to Pluto's checked scheduler oracle")
        elif flag == "--scalpriv":
            if not pluto_has_working_candldep():
                raise Reject("--scalpriv: selected Pluto Candl importer aborts on a dependent probe; requires the Candl dependence-type import fix")
            state.add_oracle_flag(flag)
            state.add_note("--scalpriv passed through only with --candldep; PolOpt still validates the output schedule under the original scalar storage semantics")
        elif flag == "--noprevector":
            state.no_prevector_seen = True
            state.add_note("--noprevector accepted; no checked vector annotation is requested")
        elif flag == "--prevector":
            state.prevector_seen = True
            state.vector = True
            state.add_note("--prevector selects the checked vector annotation route")
        elif flag == "--nounrolljam":
            state.no_unrolljam_seen = True
            state.add_note("--nounrolljam accepted; no checked unroll post pass is requested")
        elif flag == "--unrolljam":
            state.unrolljam_seen = True
            state.add_note("--unrolljam selects polopt's checked unroll-jam post pass: constant-bound loops are fully unrolled, otherwise sequential Loop IR is block/remainder unrolled and same-bound sibling loops are jam-fused through a per-candidate local validator")
        elif flag in SUPPORTED_OPTIMIZER_OPTIONS:
            state.add_oracle_flag(flag)
            state.add_note(f"{flag} passed through to Pluto's checked scheduler oracle")
        elif flag in LP_SOLVER_OPTIONS:
            if not pluto_supports_option(flag):
                raise Reject(f"{flag}: current Pluto binary does not advertise this LP/DFP option")
            if flag in LP_SOLVER_DEPENDENT_OPTIONS and not pluto_has_lp_solver_support():
                raise Reject(f"{flag}: requires a GLPK- or Gurobi-enabled Pluto binary")
            state.add_oracle_flag(flag)
            state.add_note(f"{flag} passed through to Pluto's checked scheduler oracle")
        elif flag in SUPPORTED_VALUE_OPTIONS:
            assert value is not None
            try:
                parsed = int(value)
            except ValueError as exc:
                if flag in NONNEGATIVE_VALUE_OPTIONS:
                    raise Reject(f"{flag}: value must be a non-negative integer") from exc
                raise Reject(f"{flag}: value must be a positive integer") from exc
            if flag in NONNEGATIVE_VALUE_OPTIONS and parsed < 0:
                raise Reject(f"{flag}: value must be a non-negative integer")
            if flag not in NONNEGATIVE_VALUE_OPTIONS and parsed <= 0:
                raise Reject(f"{flag}: value must be a positive integer")
            state.add_oracle_flag(f"{flag}={value}")
            if flag == "--ufactor":
                state.add_note(
                    f"{flag}={value} accepted as Pluto's unroll/tile factor; "
                    "it is passed to the scheduler oracle only with --determine-tile-size"
                )
            else:
                state.add_note(f"{flag}={value} passed through to Pluto's checked scheduler oracle")
        elif flag in ACCEPTED_NOOPS:
            state.add_note(f"{flag} accepted as a no-op for the checked polopt route")
        elif flag == "--unroll":
            raise Reject("--unroll: use explicit --unrolljam for polopt's checked constant-bound unroll subset")
        elif flag in VALUE_OPTIONS:
            if flag in ("--cloogf", "--cloogl", "--codegen-context", "-o"):
                raise Reject(f"{flag}: output/codegen shaping is outside the polopt checked route")
            raise Reject(f"{flag}: value {value!r} is not exposed through the checked polopt route")
        else:
            raise Reject(f"{flag}: not in the current Pluto-compatible checked subset")
    return state


def polopt_args_for_state(state: PlutoFlagState) -> list[str]:
    if state.tile_seen and state.notile_seen:
        raise Reject("--tile and --notile are both present; this wrapper rejects contradictory phase controls")
    if state.parallel_seen and state.no_parallel_seen:
        raise Reject("--parallel and --noparallel are both present; this wrapper rejects contradictory phase controls")
    if state.diamond_seen and state.nodiamond_seen:
        raise Reject("--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present; this wrapper rejects contradictory phase controls")
    if state.intratileopt_seen and state.no_intratileopt_seen:
        raise Reject("--intratileopt and --nointratileopt are both present; this wrapper rejects contradictory tile-schedule controls")
    if state.prevector_seen and state.no_prevector_seen:
        raise Reject("--prevector and --noprevector are both present; this wrapper rejects contradictory vector controls")
    if state.unrolljam_seen and state.no_unrolljam_seen:
        raise Reject("--unrolljam and --nounrolljam are both present; this wrapper rejects contradictory unroll controls")
    oracle_flags = state.oracle_flags or []
    if "--lastwriter" in oracle_flags and "--nolastwriter" in oracle_flags:
        raise Reject("--lastwriter and --nolastwriter are both present; this wrapper rejects contradictory dependence controls")
    if state.isldep_seen and state.candldep_seen:
        raise Reject("--isldep and --candldep are both present; Pluto accepts only one dependence tester")
    if "--scalpriv" in oracle_flags and not state.candldep_seen:
        raise Reject("--scalpriv requires --candldep in the checked polopt subset")
    if "--lastwriter" in oracle_flags and state.candldep_seen:
        raise Reject("--lastwriter is only supported with Pluto's ISL dependence tester, not --candldep")
    if not (state.intratileopt_seen or state.no_intratileopt_seen):
        raise Reject("Pluto enables --intratileopt by default; pass --nointratileopt or --intratileopt explicitly")
    if not state.no_prevector_seen:
        state.vector = True
        state.add_note("Pluto --prevector is represented as checked vector annotation over the same doall certificate used by --parallel")
    if not (state.no_unrolljam_seen or state.unrolljam_seen):
        raise Reject("Pluto enables --unrolljam by default; pass --nounrolljam or explicit --unrolljam")
    if not state.parallel and not state.no_parallel_seen:
        raise Reject("Pluto enables --parallel by default; pass --noparallel or --parallel explicitly")
    if state.vector and state.parallel:
        raise Reject("--prevector/--vector cannot be combined with --parallel in the current checked annotation surface")
    if state.unrolljam_seen and (state.vector or state.parallel):
        raise Reject("--unrolljam currently applies only to sequential Loop IR routes in polopt")
    if not state.diamond_tile and not state.nodiamond_seen:
        raise Reject("Pluto enables --diamond-tile by default; pass --nodiamond-tile or --diamond-tile explicitly")
    identity_tiled = state.identity and state.tile_seen and state.tile
    if state.identity and state.parallel and not identity_tiled:
        raise Reject("--parallel with --identity requires --tile so the checked identity-tiling route has a Pluto loop hint")
    if state.identity and state.vector and not identity_tiled:
        raise Reject("--prevector with --identity requires --tile so the checked identity-tiling route has a Pluto loop hint")
    if identity_tiled and state.diamond_tile:
        raise Reject("--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity")
    if state.identity and not state.notile_seen and not identity_tiled:
        raise Reject("--identity: current Pluto keeps tiling enabled by default; use --identity --notile for polopt's no-tiling identity route")
    if state.second_level_tile and not state.tile:
        raise Reject("--second-level-tile requires tiling and cannot be combined with --notile")
    if state.second_level_tile and state.identity and not identity_tiled:
        raise Reject("--second-level-tile with --identity requires --tile")
    has_cache_or_data_size = any(
        flag.startswith("--cache-size=") or flag.startswith("--data-element-size=")
        for flag in oracle_flags
    )
    has_ufactor = any(flag.startswith("--ufactor=") for flag in oracle_flags)
    has_determine_tile_size = "--determine-tile-size" in oracle_flags
    if has_cache_or_data_size and not has_determine_tile_size:
        raise Reject("--cache-size/--data-element-size require --determine-tile-size in the checked polopt subset")
    if has_ufactor and not has_determine_tile_size and not state.unrolljam_seen:
        raise Reject("--ufactor without --determine-tile-size requires --unrolljam in the checked polopt subset")
    if (has_cache_or_data_size or (has_ufactor and has_determine_tile_size)) and (state.identity or not state.tile):
        raise Reject("--cache-size/--data-element-size/--ufactor require a tiled route when used for Pluto tile-size modeling")
    if has_ufactor and not has_determine_tile_size and state.unrolljam_seen:
        state.add_note(
            "--ufactor is not passed to Pluto's scheduler oracle here; checked --unrolljam uses the verified LoopUnroll post pass"
        )

    ft_values = [flag.split("=", 1)[1] for flag in oracle_flags if flag.startswith("--ft=")]
    lt_values = [flag.split("=", 1)[1] for flag in oracle_flags if flag.startswith("--lt=")]
    if bool(ft_values) != bool(lt_values):
        raise Reject("--ft and --lt must be supplied together in the checked polopt subset")
    if ft_values and lt_values:
        ft = int(ft_values[-1])
        lt = int(lt_values[-1])
        if ft > lt:
            raise Reject("--ft must be less than or equal to --lt")
        if state.identity or not state.tile:
            raise Reject("--ft/--lt require a tiled route in the checked polopt subset")

    if state.diamond_tile:
        if not state.tile:
            raise Reject("--diamond-tile requires tiling and cannot be combined with --notile")
        if state.identity:
            raise Reject("--diamond-tile requires a Pluto tiling phase and cannot be combined with --identity")

    args: list[str] = []
    if identity_tiled:
        if state.iss:
            args.append("--iss")
        args.extend(["--identity", "--tile"])
        if state.second_level_tile:
            args.append("--second-level-tile")
    elif state.identity:
        if state.iss:
            args.append("--iss")
        args.append("--identity")
    elif not state.tile:
        args.append("--notile")
    else:
        if state.iss:
            args.append("--iss")
        if state.second_level_tile:
            args.append("--second-level-tile")
        if state.full_diamond_tile:
            args.append("--full-diamond-tile")
        elif state.diamond_tile:
            args.append("--diamond-tile")
    if state.parallel:
        args.append("--parallel")
    if state.vector:
        args.append("--vector")
    if state.unrolljam_seen:
        args.append("--const-unroll")
    return args


def scheduler_oracle_flags_for_state(state: PlutoFlagState) -> list[str]:
    oracle_flags = list(state.oracle_flags or [])
    if state.unrolljam_seen and "--determine-tile-size" not in oracle_flags:
        oracle_flags = [flag for flag in oracle_flags if not flag.startswith("--ufactor=")]
    return oracle_flags


def native_compat_args_for_state(state: PlutoFlagState) -> list[str]:
    args: list[str] = ["--pluto-compat"]
    if state.identity:
        args.append("--identity")
        if state.tile_seen and state.tile:
            args.append("--tile")
        elif not state.tile:
            args.append("--notile")
    elif state.tile:
        args.append("--tile")
    else:
        args.append("--notile")
    if state.iss:
        args.append("--iss")
    if state.second_level_tile:
        args.append("--second-level-tile")
    if state.full_diamond_tile:
        args.append("--full-diamond-tile")
    elif state.diamond_tile:
        args.append("--diamond-tile")
    else:
        args.append("--nodiamond-tile")
    if state.parallel:
        args.append("--parallel")
    else:
        args.append("--noparallel")
    args.append("--prevector" if state.vector else "--noprevector")
    args.append("--unrolljam" if state.unrolljam_seen else "--nounrolljam")
    if state.no_intratileopt_seen:
        args.append("--nointratileopt")
    if state.oracle_flags:
        args.extend(state.oracle_flags)
    if state.control_files:
        for flag, path in state.control_files:
            args.extend([flag, path])
    args.append(str(state.input_path))
    return args


def main(argv: list[str]) -> int:
    try:
        cfg, rest = parse_wrapper_args(argv)
        flags, input_path = split_flags_and_input(rest)
        state = normalize_pluto_flags(flags, input_path)
        polopt_args = polopt_args_for_state(state)
    except (Reject, ValueError) as exc:
        print(f"[pluto-compat] reject: {exc}", file=sys.stderr)
        return 2

    polopt_path = cfg.polopt if cfg.polopt.is_absolute() else ROOT / cfg.polopt
    cmd = [str(polopt_path), *native_compat_args_for_state(state)]
    if cfg.explain or cfg.dry_run:
        print("[pluto-compat] accepted", flush=True)
        print(
            "[pluto-compat] polopt args:",
            " ".join(polopt_args) if polopt_args else "<default>",
            flush=True,
        )
        scheduler_oracle_flags = scheduler_oracle_flags_for_state(state)
        post_flags = []
        if state.unrolljam_seen and "--determine-tile-size" not in (state.oracle_flags or []):
            post_flags = [flag for flag in (state.oracle_flags or []) if flag.startswith("--ufactor=")]
        if scheduler_oracle_flags:
            print(
                "[pluto-compat] pluto oracle flags:",
                " ".join(scheduler_oracle_flags),
                flush=True,
            )
        if post_flags:
            print("[pluto-compat] checked post flags:", " ".join(post_flags), flush=True)
        if state.control_files:
            print(
                "[pluto-compat] pluto control files:",
                " ".join(f"{flag}={path}" for flag, path in state.control_files),
                flush=True,
            )
        if state.notes:
            for note in state.notes:
                print(f"[pluto-compat] note: {note}", flush=True)
    if cfg.dry_run:
        return 0

    try:
        proc = subprocess.run(
            cmd,
            cwd=str(ROOT),
            text=True,
            timeout=cfg.timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        print("[pluto-compat] reject: polopt timed out", file=sys.stderr)
        return 124
    except OSError as exc:
        print(f"[pluto-compat] infrastructure error: failed to run polopt: {exc}", file=sys.stderr)
        return 127
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
