#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from pluto_versions import locate_buggy_pluto_and_polycc


PLUTO_FLAGS = [
    "--notile",
    "--nodiamond-tile",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--noparallel",
]

COMPAT_FLAGS = [
    "--notile",
    "--smartfuse",
    "--nointratileopt",
    "--nodiamond-tile",
    "--noprevector",
    "--nounrolljam",
    "--noparallel",
    "--rar",
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
    fixture_dir = repo / "tests" / "pluto-bugs" / "affine-fst-reversed"
    source = fixture_dir / "affine_fst_reversed.c"
    loop = fixture_dir / "affine_fst_reversed.loop"
    control = fixture_dir / "reversed.fst"
    polopt = repo / "polopt"
    pluto, polycc = locate_buggy_pluto_and_polycc()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists() and control.exists(), "missing affine bug fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-affine-bug-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        shutil.copy2(control, work / ".fst")

        pluto_proc = run([polycc, "--dumpscop", *PLUTO_FLAGS, work_source.name], cwd=work)
        stem = source.stem
        generated = work / f"{stem}.pluto.c"
        before = work / f"{stem}.beforescheduling.scop"
        after = work / f"{stem}.afterscheduling.scop"
        require(pluto_proc.returncode == 0, f"Pluto rejected the reproducer:\n{pluto_proc.stdout}")
        require(generated.exists() and before.exists() and after.exists(), "Pluto omitted an expected artifact")
        generated_text = generated.read_text()
        b_pos = generated_text.find("b[t2] = a[t2]")
        a_pos = generated_text.find("a[t2] = t2 + 1")
        require(b_pos >= 0 and a_pos >= 0 and b_pos < a_pos, "Pluto output did not reverse producer and consumer")
        print(
            "[pluto-affine-bug] producer: expected=consumer-before-producer "
            "actual=exit-0,reversed-statement-groups interpretation=illegal-affine-order"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run([compiler, "-O2", generated, "-o", optimized_exe])
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")
        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        optimized = parse_int_output("optimized execution", run([optimized_exe]))
        require(baseline == 100 and optimized == 0, f"unexpected results: baseline={baseline}, optimized={optimized}")
        print(
            f"[pluto-affine-bug] execution: expected={baseline} actual={optimized} "
            "consistency=mismatch"
        )

        affine = run([polopt, "--validate-affine-openscop", before, after], cwd=repo)
        require(
            affine.returncode != 0 and "overall: FAIL" in affine.stdout,
            f"PolCert affine validator accepted the reversed schedule:\n{affine.stdout}",
        )
        print(
            f"[pluto-affine-bug] affine-validator: expected=rejected "
            f"actual=exit-{affine.returncode},overall-FAIL interpretation=dependence-violation-detected"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        checked = run(
            [
                polopt,
                "--pluto-compat",
                *COMPAT_FLAGS,
                "--fusion-structure",
                control,
                loop,
            ],
            cwd=repo,
            env=polcert_env,
        )
        require(
            checked.returncode != 0
            and "[alarm] requested checked optimization was rejected" in checked.stdout
            and "== Optimized Loop ==" not in checked.stdout,
            f"PolCert compatibility route did not fail closed:\n{checked.stdout}",
        )
        print(
            f"[pluto-affine-bug] checked-pipeline: expected=rejected,no-output "
            f"actual=exit-{checked.returncode},alarm interpretation=fail-closed"
        )

    print("[pluto-affine-bug] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-affine-bug] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
