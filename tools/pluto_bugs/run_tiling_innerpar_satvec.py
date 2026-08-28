#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


PLUTO_FLAGS = [
    "--identity",
    "--tile",
    "--parallel",
    "--innerpar",
    "--nodiamond-tile",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
]


def run(cmd, *, cwd=None, env=None, timeout=30):
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
    fixture_dir = repo / "tests" / "pluto-bugs" / "tiling-innerpar-satvec"
    source = fixture_dir / "tiling_innerpar_satvec.c"
    loop = fixture_dir / "tiling_innerpar_satvec.loop"
    tile_sizes = fixture_dir / "tile.sizes"
    polopt = repo / "polopt"
    pluto, polycc = locate_pluto()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists() and tile_sizes.exists(), "missing innerpar bug fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-innerpar-bug-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        shutil.copy2(tile_sizes, work / "tile.sizes")

        pluto_proc = run([polycc, "--dumpscop", *PLUTO_FLAGS, work_source.name], cwd=work)
        stem = source.stem
        generated = work / f"{stem}.pluto.c"
        require(pluto_proc.returncode == 0, f"Pluto rejected the reproducer:\n{pluto_proc.stdout}")
        require(generated.exists(), "Pluto omitted the generated C artifact")
        generated_text = generated.read_text()
        require(
            "#pragma omp parallel for" in generated_text and "for (t4=" in generated_text,
            "Pluto output did not parallelize the dependent t4 tile loop",
        )
        print(
            "[pluto-tiling-bug] producer: expected=parallel-dependent-t4 "
            "actual=exit-0,omp-t4 interpretation=stale-satisfaction-metadata"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run([compiler, "-O2", "-fopenmp", generated, "-o", optimized_exe])
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")
        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        omp_env = os.environ.copy()
        omp_env.update({"OMP_NUM_THREADS": "4", "OMP_DYNAMIC": "FALSE"})
        optimized = [
            parse_int_output("optimized execution", run([optimized_exe], env=omp_env))
            for _ in range(5)
        ]
        require(baseline == 310235039, f"unexpected baseline result: {baseline}")
        require(any(value != baseline for value in optimized), f"unsafe executions matched baseline: {optimized}")
        print(
            f"[pluto-tiling-bug] execution: expected={baseline} "
            f"actual={','.join(map(str, optimized))} consistency=mismatch"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        checked = run([polopt, *PLUTO_FLAGS, loop], cwd=work, env=polcert_env)
        require(
            checked.returncode == 0
            and "[tiling-validation] route=permutable-band" in checked.stdout
            and "[parallel-validation] status=skipped" in checked.stdout
            and "reason=no-certifiable-dimension" in checked.stdout
            and "parallel for" not in checked.stdout,
            f"PolCert non-strict route did not retain safe sequential tiling:\n{checked.stdout}",
        )
        print(
            "[pluto-tiling-bug] checked-pipeline: expected=tiling-accepted,parallel-skipped "
            "actual=exit-0,permutable-band,sequential interpretation=unsafe-overlay-removed"
        )

        strict = run([polopt, *PLUTO_FLAGS, "--parallel-strict", loop], cwd=work, env=polcert_env)
        require(
            strict.returncode != 0
            and "[parallel-validation] status=rejected" in strict.stdout
            and "[alarm] requested checked optimization was rejected" in strict.stdout
            and "== Optimized Loop ==" not in strict.stdout,
            f"PolCert strict route did not fail closed:\n{strict.stdout}",
        )
        print(
            f"[pluto-tiling-bug] strict-pipeline: expected=rejected,no-output "
            f"actual=exit-{strict.returncode},alarm interpretation=fail-closed"
        )

    print("[pluto-tiling-bug] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-tiling-bug] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
