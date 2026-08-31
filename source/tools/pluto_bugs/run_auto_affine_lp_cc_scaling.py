#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from pluto_versions import locate_buggy_pluto_and_polycc


PLUTO_FLAGS = [
    "--maxfuse",
    "--lp",
    "--notile",
    "--noparallel",
    "--noprevector",
    "--nounrolljam",
    "--nointratileopt",
    "--nodiamond-tile",
]

BASELINE_RESULT = 802469374803681347
MISCOMPILED_RESULT = 11412027514774867379


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


def parse_uint64_output(label, proc):
    require(proc.returncode == 0, f"{label} failed with exit {proc.returncode}:\n{proc.stdout}")
    try:
        value = int(proc.stdout.strip())
    except ValueError as exc:
        raise AssertionError(f"{label} returned non-integer output: {proc.stdout!r}") from exc
    require(0 <= value < 2**64, f"{label} returned a non-uint64 value: {value}")
    return value


def main():
    repo = Path(__file__).resolve().parents[2]
    fixture_dir = repo / "tests" / "pluto-bugs" / "auto-affine-lp-cc-scaling"
    source = fixture_dir / "auto_affine_lp_cc_scaling.c"
    loop = fixture_dir / "auto_affine_lp_cc_scaling.loop"
    polopt = repo / "polopt"
    pluto, polycc = locate_buggy_pluto_and_polycc()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists(), "missing automatic affine fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-auto-affine-bug-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)
        require(
            not any((work / name).exists() for name in (".fst", ".precut", "skipdeps.txt")),
            "unexpected Pluto control file in the test directory",
        )

        pluto_proc = run([polycc, "--dumpscop", *PLUTO_FLAGS, work_source.name], cwd=work)
        stem = source.stem
        generated = work / f"{stem}.pluto.c"
        before = work / f"{stem}.beforescheduling.scop"
        after = work / f"{stem}.afterscheduling.scop"
        require(
            pluto_proc.returncode == 0,
            f"Pluto did not produce the automatic LP schedule:\n{pluto_proc.stdout}",
        )
        require(generated.exists(), "Pluto returned success without generated C output")
        require(before.exists() and after.exists(), "Pluto omitted the affine phase dumps")
        require(
            "T(S1): (2i+j, i" in pluto_proc.stdout
            and "T(S2): (9i+3j, i" in pluto_proc.stdout
            and "T(S3): (8i+4j+4, i" in pluto_proc.stdout
            and "T(S4): (9i+3j+6, i" in pluto_proc.stdout,
            f"Pluto no longer reports the expected automatic affine schedule:\n{pluto_proc.stdout}",
        )
        print(
            "[pluto-auto-affine-lp] scheduler: expected=automatic-two-component-lp "
            "actual=exit-0,illegal-S3-to-S1-order control-files=none"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-std=c11", "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run([compiler, "-std=c11", "-O2", generated, "-o", optimized_exe])
        require(optimized_build.returncode == 0, f"optimized build failed:\n{optimized_build.stdout}")

        baseline = parse_uint64_output("baseline execution", run([baseline_exe]))
        optimized = parse_uint64_output("optimized execution", run([optimized_exe]))
        require(baseline == BASELINE_RESULT, f"unexpected baseline result: {baseline}")
        require(
            optimized == MISCOMPILED_RESULT,
            f"Pluto output changed: expected={MISCOMPILED_RESULT}, actual={optimized}",
        )
        print(
            f"[pluto-auto-affine-lp] execution: expected={baseline} actual={optimized} "
            "consistency=mismatch"
        )

        affine = run([polopt, "--validate-affine-openscop", before, after], cwd=repo)
        require(
            affine.returncode != 0 and "overall: FAIL" in affine.stdout,
            f"PolCert affine validator accepted Pluto's illegal schedule:\n{affine.stdout}",
        )
        print(
            f"[pluto-auto-affine-lp] affine-validator: expected=rejected "
            f"actual=exit-{affine.returncode},overall-FAIL "
            "interpretation=automatic-schedule-dependence-violation"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))
        compat_flags = [
            "--pluto-compat",
            "--notile",
            "--maxfuse",
            "--lp",
            "--nointratileopt",
            "--nodiamond-tile",
            "--noprevector",
            "--nounrolljam",
            "--noparallel",
        ]
        checked = run([polopt, *compat_flags, loop], cwd=repo, env=polcert_env)
        require(
            checked.returncode != 0
            and "[alarm] requested checked optimization was rejected" in checked.stdout
            and "== Optimized Loop ==" not in checked.stdout,
            f"PolCert's default no-RAR route did not reject the bad candidate:\n{checked.stdout}",
        )
        print(
            f"[pluto-auto-affine-lp] checked-default: expected=no-rar,rejected,no-output "
            f"actual=exit-{checked.returncode},alarm interpretation=pluto-default-aligned-fail-closed"
        )

        checked_rar = run(
            [polopt, *compat_flags, "--rar", loop], cwd=repo, env=polcert_env
        )
        require(
            checked_rar.returncode == 0
            and "== Optimized Loop ==" in checked_rar.stdout
            and "[alarm]" not in checked_rar.stdout,
            f"PolCert did not forward explicit --rar to obtain the legal candidate:\n{checked_rar.stdout}",
        )
        print(
            "[pluto-auto-affine-lp] checked-explicit-rar: expected=rar-forwarded,accepted "
            "actual=exit-0,optimized-loop interpretation=explicit-oracle-policy-effective"
        )

    print("[pluto-auto-affine-lp] OK")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-auto-affine-lp] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
