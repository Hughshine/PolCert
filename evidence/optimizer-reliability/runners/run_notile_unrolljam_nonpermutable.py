#!/usr/bin/env python3

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from pluto_versions import locate_buggy_pluto_and_polycc


PLUTO_FLAGS = [
    "--identity",
    "--notile",
    "--nodiamond-tile",
    "--nointratileopt",
    "--noprevector",
    "--unrolljam",
    "--ufactor=2",
    "--noparallel",
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


def parse_int_output(label, proc):
    require(proc.returncode == 0, f"{label} failed with exit {proc.returncode}:\n{proc.stdout}")
    try:
        return int(proc.stdout.strip())
    except ValueError as exc:
        raise AssertionError(f"{label} returned non-integer output: {proc.stdout!r}") from exc


def main():
    repo = Path(__file__).resolve().parents[2]
    fixture_dir = repo / "tests" / "pluto-bugs" / "notile-unrolljam-nonpermutable"
    source = fixture_dir / "notile_unrolljam_nonpermutable.c"
    loop = fixture_dir / "notile_unrolljam_nonpermutable.loop"
    polopt = repo / "polopt"
    pluto, polycc = locate_buggy_pluto_and_polycc()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists(), "missing unroll-jam bug fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-unrolljam-bug-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)

        pluto_proc = run([polycc, *PLUTO_FLAGS, work_source.name], cwd=work)
        generated = work / "notile_unrolljam_nonpermutable.pluto.c"
        require(
            pluto_proc.returncode == 0,
            f"Pluto did not silently accept the reproducer:\n{pluto_proc.stdout}",
        )
        require(generated.exists(), "Pluto returned success without generated C output")
        generated_text = generated.read_text()
        unsafe_pair = re.compile(
            r"a\[t2\]\[t4\]\[t6\]\[t8\].*?;\s*"
            r"a\[t2\]\[t4\]\[\(t6\+1\)\]\[t8\].*?;"
        )
        require(
            unsafe_pair.search(generated_text),
            "Pluto output no longer contains the expected unsafe jammed pair",
        )
        print(
            "[pluto-unrolljam-bug] producer: expected=success-with-unsafe-jam "
            "actual=exit-0,adjacent-j-pair"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run([compiler, "-O2", generated, "-o", optimized_exe])
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")

        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        optimized = parse_int_output("optimized execution", run([optimized_exe]))
        require(baseline == 15, f"unexpected baseline result: {baseline}")
        require(
            optimized != baseline,
            f"unsafe Pluto execution unexpectedly matched the baseline: {optimized}",
        )
        print(
            f"[pluto-unrolljam-bug] execution: expected={baseline} "
            f"actual={optimized} consistency=mismatch"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        checked = run([polopt, *PLUTO_FLAGS, loop], cwd=repo, env=polcert_env)
        require(checked.returncode == 0, f"PolCert checked route failed:\n{checked.stdout}")
        safe_k_loop = "for i3 in range(0, 6)"
        require(
            checked.stdout.count(safe_k_loop) == 3
            and "A[i0][i1][((2 * i2) + 1)][i3]" in checked.stdout
            and "A[i0][i1][((2 * i2) + 2)][i3]" in checked.stdout,
            f"PolCert did not preserve separate k loops around the unrolled bodies:\n{checked.stdout}",
        )
        print(
            "[pluto-unrolljam-bug] polcert: expected=no-unsafe-jam "
            "actual=exit-0,separate-k-loops interpretation=jam-candidate-rejected"
        )

    print("[pluto-unrolljam-bug] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-unrolljam-bug] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
