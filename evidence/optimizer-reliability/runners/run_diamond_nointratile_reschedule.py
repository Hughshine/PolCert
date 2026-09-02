#!/usr/bin/env python3

import os
import shutil
import subprocess
import tempfile
from pathlib import Path


PLUTO_FLAGS = [
    "--tile",
    "--diamond-tile",
    "--nointratileopt",
    "--noparallel",
    "--noprevector",
    "--nounrolljam",
]

POLCERT_FLAGS = [
    "--pluto-compat",
    "--tile",
    "--smartfuse",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--rar",
    "--diamond-tile",
    "--noparallel",
    "--tile-sizes-file",
    "tests/pluto-bugs/diamond-nointratile-reschedule/tile.sizes",
]


def run(cmd, *, cwd=None, env=None, timeout=120):
    return subprocess.run(
        [str(arg) for arg in cmd],
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=timeout,
        check=False,
    )


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def locate_pluto():
    configured = os.environ.get("POLCERT_PLUTO")
    if configured:
        pluto = Path(configured).resolve()
    elif Path("/pluto/tool/pluto").exists():
        pluto = Path("/pluto/tool/pluto")
    else:
        found = shutil.which("pluto")
        if found is None:
            raise AssertionError("cannot locate Pluto; set POLCERT_PLUTO")
        pluto = Path(found).resolve()

    configured_polycc = os.environ.get("POLCERT_POLYCC")
    if configured_polycc:
        polycc = Path(configured_polycc).resolve()
    elif pluto.parent.name == "tool" and (pluto.parent.parent / "polycc").exists():
        polycc = pluto.parent.parent / "polycc"
    else:
        found = shutil.which("polycc")
        if found is None:
            raise AssertionError("cannot locate polycc; set POLCERT_POLYCC")
        polycc = Path(found).resolve()
    return pluto, polycc


def parse_int_output(label, proc):
    require(proc.returncode == 0, f"{label} failed with exit {proc.returncode}:\n{proc.stdout}")
    try:
        return int(proc.stdout.strip())
    except ValueError as exc:
        raise AssertionError(f"{label} returned non-integer output: {proc.stdout!r}") from exc


def main():
    repo = Path(__file__).resolve().parents[2]
    fixture = repo / "tests" / "pluto-bugs" / "diamond-nointratile-reschedule"
    source = fixture / "diamond_nointratile.c"
    tile_sizes = fixture / "tile.sizes"
    polopt = repo / "polopt"
    pluto, polycc = locate_pluto()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and tile_sizes.exists(), "missing diamond regression fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-diamond-nointra-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        shutil.copy2(tile_sizes, work / "tile.sizes")

        producer = run([polycc, *PLUTO_FLAGS, work_source.name], cwd=work)
        generated = work / f"{source.stem}.pluto.c"
        require(producer.returncode == 0 and generated.exists(), f"Pluto failed:\n{producer.stdout}")
        require(
            "[Pluto] After intra_tile reschedule" in producer.stdout,
            "diamond hyperplane restore did not run under --nointratileopt",
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O0", work_source, "-o", baseline_exe])
        optimized_build = run([compiler, "-O0", generated, "-o", optimized_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")
        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        optimized = parse_int_output("fixed Pluto execution", run([optimized_exe]))
        require(baseline == 20 and optimized == baseline, f"unexpected results: {baseline}, {optimized}")
        print(
            f"[pluto-diamond-nointra] producer: expected={baseline} actual={optimized} "
            "consistency=match interpretation=mandatory-diamond-restore-ran"
        )

        env = os.environ.copy()
        env["POLCERT_PLUTO"] = str(pluto)
        env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        checked = run(
            [polopt, *POLCERT_FLAGS, fixture / "input.loop"],
            cwd=repo,
            env=env,
            timeout=120,
        )
        require(
            checked.returncode == 2
            and "[tiling-validation] route=rejected" in checked.stdout
            and "[alarm] requested checked optimization was rejected" in checked.stdout,
            "checked PolCert route did not reject the mixed-scalar diamond candidate:\n"
            + checked.stdout,
        )
        require("== Optimized Loop ==" not in checked.stdout, "rejected route emitted an optimized loop")
        print(
            "[pluto-diamond-nointra] checked-pipeline: expected=reject-mixed-scalar-candidate "
            "actual=rejected-no-output interpretation=formal-tiling-boundary-failed-closed"
        )

    print("[pluto-diamond-nointra] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-diamond-nointra] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
