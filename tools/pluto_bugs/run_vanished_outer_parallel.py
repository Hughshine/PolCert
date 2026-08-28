#!/usr/bin/env python3

import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


PLUTO_FLAGS = [
    "--notile",
    "--nodiamond-tile",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--parallel",
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
    fixture_dir = repo / "tests" / "pluto-bugs" / "vanished-outer-parallel"
    source = fixture_dir / "vanished_outer_parallel.c"
    loop = fixture_dir / "vanished_outer_parallel.loop"
    polopt = repo / "polopt"
    pluto, polycc = locate_pluto()
    compiler = os.environ.get("CC", "gcc")

    require(polopt.exists(), f"missing PolCert executable: {polopt}")
    require(source.exists() and loop.exists(), "missing vanished-loop fixtures")

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-miscompile-") as tmp:
        work = Path(tmp)
        work_source = work / source.name
        shutil.copy2(source, work_source)

        pluto_proc = run([polycc, *PLUTO_FLAGS, work_source.name], cwd=work)
        generated = work / "vanished_outer_parallel.pluto.c"
        require(
            pluto_proc.returncode == 0,
            f"Pluto did not silently accept the reproducer:\n{pluto_proc.stdout}",
        )
        require(generated.exists(), "Pluto returned success without generated C output")
        generated_text = generated.read_text()
        require(
            "#pragma omp parallel for" in generated_text and "for (t2=" in generated_text,
            "Pluto output did not parallelize the dependent surviving t2 loop",
        )
        print(
            "[pluto-miscompile] producer: expected=success-with-inner-OpenMP "
            "actual=exit-0,parallel-t2 interpretation=unsafe-loop-substitution"
        )

        baseline_exe = work / "baseline"
        optimized_exe = work / "optimized"
        baseline_build = run([compiler, "-O2", work_source, "-o", baseline_exe])
        require(baseline_build.returncode == 0, f"baseline build failed:\n{baseline_build.stdout}")
        optimized_build = run(
            [compiler, "-O2", "-fopenmp", generated, "-o", optimized_exe]
        )
        require(
            optimized_build.returncode == 0,
            f"optimized build failed:\n{optimized_build.stdout}",
        )

        baseline = parse_int_output("baseline execution", run([baseline_exe]))
        require(baseline == 10000, f"unexpected baseline result: {baseline}")
        omp_env = os.environ.copy()
        omp_env.update({"OMP_NUM_THREADS": "4", "OMP_DYNAMIC": "FALSE"})
        optimized = [
            parse_int_output("optimized execution", run([optimized_exe], env=omp_env))
            for _ in range(3)
        ]
        require(
            any(value != baseline for value in optimized),
            f"unsafe OpenMP executions unexpectedly matched the baseline: {optimized}",
        )
        print(
            f"[pluto-miscompile] execution: expected={baseline} "
            f"actual={','.join(map(str, optimized))} consistency=mismatch"
        )

        polcert_env = os.environ.copy()
        polcert_env["POLCERT_PLUTO"] = str(pluto)
        polcert_env.setdefault("COMPCERT_CONFIG", str(repo / "polcert.ini"))

        strict = run(
            [polopt, *PLUTO_FLAGS[:-1], "--parallel", "--parallel-strict", loop],
            cwd=repo,
            env=polcert_env,
        )
        require(strict.returncode != 0, "PolCert strict hinted route accepted Pluto's vanished-loop hint")
        require(
            "[parallel-validation] status=rejected" in strict.stdout
            and "[alarm] requested checked optimization was rejected" in strict.stdout
            and "== Optimized Loop ==" not in strict.stdout,
            f"PolCert strict rejection was incomplete:\n{strict.stdout}",
        )
        print(
            f"[pluto-miscompile] polcert-hint: expected=rejected "
            f"actual=exit-{strict.returncode},no-output interpretation=fail-closed"
        )

        actual_inner = run(
            [polopt, "--notile", "--parallel-current", "1", loop],
            cwd=repo,
            env=polcert_env,
        )
        require(actual_inner.returncode != 0, "PolCert accepted Pluto's actual dependent t2 loop")
        require(
            "source=explicit-current reason=not-certifiable-or-out-of-range"
            in actual_inner.stdout,
            f"PolCert did not report rejection of current dimension 1:\n{actual_inner.stdout}",
        )
        print(
            f"[pluto-miscompile] polcert-inner-loop: expected=rejected "
            f"actual=exit-{actual_inner.returncode} interpretation=dependence-detected"
        )

    print("[pluto-miscompile] OK (white-box defect reproduced and rejected)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, subprocess.TimeoutExpired) as exc:
        print(f"[pluto-miscompile] FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
