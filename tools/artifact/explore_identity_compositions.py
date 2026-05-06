#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import tempfile
from dataclasses import dataclass


ROOT = pathlib.Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
POLCERT = ROOT / "polcert"
PLUTO = pathlib.Path("/pluto/tool/pluto")

COMMON_DISABLED = [
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--noparallel",
]


@dataclass(frozen=True)
class Case:
    name: str
    loop: pathlib.Path


CASES = {
    "fusion7": Case("fusion7", ROOT / "tests/polopt-regression/inputs/fusion7.loop"),
    "wavefront": Case("wavefront", ROOT / "tests/polopt-regression/inputs/wavefront.loop"),
}

IDENTITY_TILE_ARGS = [
    "--pluto-compat",
    "--identity",
    "--tile",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--nodiamond-tile",
    "--noparallel",
]


def run(cmd: list[str], *, cwd: pathlib.Path = ROOT, timeout: int = 30) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        check=False,
        timeout=timeout,
    )


def optimized_loop_text(output: str) -> str:
    marker = "== Optimized Loop =="
    pos = output.find(marker)
    return output[pos:] if pos >= 0 else output


def export_scop(case: Case, out_dir: pathlib.Path) -> pathlib.Path:
    proc = run([str(POLOPT), "--dump-extracted-openscop", "--extract-only", str(case.loop)])
    if proc.returncode != 0:
        raise RuntimeError(f"{case.name}: OpenScop export failed: {proc.stderr}")
    path = out_dir / f"{case.name}.scop"
    path.write_text(proc.stdout)
    return path


def run_pluto(scop: pathlib.Path, flags: list[str], out_dir: pathlib.Path, stem: str) -> dict[str, object]:
    local = out_dir / f"{stem}.scop"
    shutil.copyfile(scop, local)
    proc = run(
        [str(PLUTO), "--dumpscop", "--readscop", *flags, local.name],
        cwd=out_dir,
    )
    c_path = pathlib.Path(str(local) + ".pluto.c")
    after = pathlib.Path(str(local) + ".afterscheduling.scop")
    mid = pathlib.Path(str(local) + ".midtransform.scop")
    post = pathlib.Path(str(local) + ".posttile.scop")
    return {
        "exit": proc.returncode,
        "stdout": proc.stdout[-1000:],
        "stderr": proc.stderr[-1000:],
        "c_path": str(c_path),
        "c_text": c_path.read_text() if c_path.exists() else "",
        "after": str(after) if after.exists() else None,
        "mid": str(mid) if mid.exists() else None,
        "post": str(post) if post.exists() else None,
    }


def validate_second_level(scop: pathlib.Path, after: str | None) -> dict[str, object]:
    if after is None:
        return {"ok": False, "reason": "missing afterscheduling scop"}
    proc = run([str(POLCERT), "--second-level-tile", str(scop), after])
    return {"ok": proc.returncode == 0, "exit": proc.returncode, "output": (proc.stdout + proc.stderr).strip()}


def validate_diamond(scop: pathlib.Path, mid: str | None, post: str | None, after: str | None) -> dict[str, object]:
    if mid is None or post is None or after is None:
        return {"ok": False, "reason": "missing diamond phase scop"}
    proc = run([str(POLCERT), str(scop), mid, post, after])
    return {"ok": proc.returncode == 0, "exit": proc.returncode, "output": (proc.stdout + proc.stderr).strip()}


def run_polopt(args: list[str], case: Case) -> dict[str, object]:
    proc = run([str(POLOPT), *args, str(case.loop)])
    stderr_lines = [line for line in proc.stderr.splitlines() if line.strip()]
    return {
        "exit": proc.returncode,
        "stdout": proc.stdout[-2000:],
        "stderr_first_line": stderr_lines[0] if stderr_lines else "",
        "stderr_tail": proc.stderr[-2000:],
    }


def run_polopt_fixture(args: list[str], loop: pathlib.Path, timeout: int = 30) -> dict[str, object]:
    try:
        proc = run([str(POLOPT), *args, str(loop)], timeout=timeout)
        output = proc.stdout + proc.stderr
        return {
            "exit": proc.returncode,
            "optimized": optimized_loop_text(output),
            "timed_out": False,
        }
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + (exc.stderr or "")
        return {
            "exit": 124,
            "optimized": optimized_loop_text(output),
            "timed_out": True,
        }


def classify_c(text: str) -> dict[str, bool]:
    return {
        "has_first_level_32": "32*" in text or "32 *" in text,
        "has_second_level_256": "256" in text,
        "has_ratio_8": "8*" in text or "8 *" in text,
        "has_diamond_macro_hint": "zT" in text,
    }


def explore_second_level(case: Case, out_dir: pathlib.Path) -> dict[str, object]:
    scop = export_scop(case, out_dir)
    ordinary = run_pluto(
        scop,
        ["--identity", "--tile", "--nodiamond-tile", *COMMON_DISABLED],
        out_dir,
        f"{case.name}.identity.tile",
    )
    second = run_pluto(
        scop,
        ["--identity", "--tile", "--second-level-tile", "--nodiamond-tile", *COMMON_DISABLED],
        out_dir,
        f"{case.name}.identity.second",
    )
    polopt_reject = run_polopt(["--identity-tiled", "--second-level-tile"], case)
    legacy = run_polopt(["--legacy-generic-tiling", "--second-level-tile"], case)
    return {
        "case": case.name,
        "mode": "identity-second-level",
        "pluto_second_level_c": classify_c(str(second["c_text"])),
        "pluto_differs_from_identity_tile": ordinary["c_text"] != second["c_text"],
        "polcert_second_level_validation": validate_second_level(scop, second["after"]),
        "polopt_identity_second_level": polopt_reject,
        "polopt_legacy_generic_second_level_c": classify_c(legacy["stdout"]),
    }


def explore_diamond(case: Case, out_dir: pathlib.Path) -> dict[str, object]:
    scop = export_scop(case, out_dir)
    ordinary = run_pluto(
        scop,
        ["--identity", "--tile", "--nodiamond-tile", *COMMON_DISABLED],
        out_dir,
        f"{case.name}.identity.tile",
    )
    diamond = run_pluto(
        scop,
        ["--identity", "--tile", "--diamond-tile", *COMMON_DISABLED],
        out_dir,
        f"{case.name}.identity.diamond",
    )
    polopt_reject = run_polopt(
        [
            "--pluto-compat",
            "--identity",
            "--tile",
            "--diamond-tile",
            "--nointratileopt",
            "--noprevector",
            "--nounrolljam",
            "--noparallel",
        ],
        case,
    )
    return {
        "case": case.name,
        "mode": "identity-diamond",
        "pluto_diamond_c": classify_c(str(diamond["c_text"])),
        "pluto_differs_from_identity_tile": ordinary["c_text"] != diamond["c_text"],
        "polcert_diamond_validation": validate_diamond(scop, diamond["mid"], diamond["post"], diamond["after"]),
        "polopt_identity_diamond": polopt_reject,
    }


def explore_identity_iss_search(limit: int | None) -> dict[str, object]:
    fixtures = sorted((ROOT / "tests/polopt-regression/inputs").glob("*.loop"))
    if limit is not None:
        fixtures = fixtures[:limit]

    interesting = []
    counts = {
        "both_success_same_output": 0,
        "both_success_different_output": 0,
        "iss_only_success": 0,
        "noiss_only_success": 0,
        "both_failed": 0,
        "timeouts": 0,
    }
    for fixture in fixtures:
        noiss = run_polopt_fixture(IDENTITY_TILE_ARGS, fixture)
        iss = run_polopt_fixture([*IDENTITY_TILE_ARGS, "--iss"], fixture)
        if noiss["timed_out"] or iss["timed_out"]:
            counts["timeouts"] += 1

        noiss_ok = noiss["exit"] == 0
        iss_ok = iss["exit"] == 0
        status = None
        if noiss_ok and iss_ok:
            if noiss["optimized"] == iss["optimized"]:
                counts["both_success_same_output"] += 1
            else:
                counts["both_success_different_output"] += 1
                status = "both-success-different-output"
        elif (not noiss_ok) and iss_ok:
            counts["iss_only_success"] += 1
            status = "iss-only-success"
        elif noiss_ok and not iss_ok:
            counts["noiss_only_success"] += 1
            status = "noiss-only-success"
        else:
            counts["both_failed"] += 1

        if status is not None and len(interesting) < 20:
            interesting.append(
                {
                    "fixture": str(fixture.relative_to(ROOT)),
                    "status": status,
                    "noiss_exit": noiss["exit"],
                    "iss_exit": iss["exit"],
                    "noiss_head": str(noiss["optimized"])[:300],
                    "iss_head": str(iss["optimized"])[:300],
                }
            )

    return {
        "mode": "identity-iss-sensitive-search",
        "fixtures_checked": len(fixtures),
        "interesting_definition": "interesting means ISS-only success, no-ISS-only success, or both routes succeeding with different optimized loops",
        "counts": counts,
        "interesting": interesting,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output-root", type=pathlib.Path)
    ap.add_argument(
        "--identity-iss-limit",
        type=int,
        default=None,
        help="limit the regression fixtures searched for ISS-sensitive identity tiling",
    )
    args = ap.parse_args()

    if not POLOPT.exists() or not POLCERT.exists() or not PLUTO.exists():
        raise SystemExit("missing polopt, polcert, or Pluto binary")

    if args.output_root is None:
        tmp = tempfile.TemporaryDirectory(prefix="polcert-identity-compositions-")
        out_dir = pathlib.Path(tmp.name)
    else:
        tmp = None
        out_dir = args.output_root
        out_dir.mkdir(parents=True, exist_ok=True)

    results = [
        explore_second_level(CASES["fusion7"], out_dir),
        explore_diamond(CASES["wavefront"], out_dir),
        explore_identity_iss_search(args.identity_iss_limit),
    ]
    print(json.dumps({"output_root": str(out_dir), "results": results}, indent=2, sort_keys=True))
    if tmp is not None:
        tmp.cleanup()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
