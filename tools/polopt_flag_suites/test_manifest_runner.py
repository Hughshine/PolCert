#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import subprocess
import tempfile
from unittest import mock

import manifest_runner


def evaluate_failure(stdout: str) -> str | None:
    with tempfile.TemporaryDirectory(prefix="polcert-manifest-runner-") as tmp:
        fixture = pathlib.Path(tmp) / "input.loop"
        fixture.write_text("dummy\n")
        completed = subprocess.CompletedProcess(
            args=["polopt"],
            returncode=1,
            stdout=stdout,
            stderr="Parallel validation failed\n",
        )
        with mock.patch.object(
            manifest_runner,
            "run_polopt",
            return_value=completed,
        ):
            return manifest_runner.evaluate_check(
                {"input": fixture},
                pathlib.Path("./polopt"),
                {
                    "name": "synthetic-rejection",
                    "fixture": "input",
                    "expect": "failure",
                    "needle": "Parallel validation failed",
                },
                stderr_needles_exactly_once=False,
                timeout=1,
            )


def main() -> int:
    ordinary_failure = evaluate_failure("")
    if ordinary_failure is not None:
        raise AssertionError(
            f"ordinary rejection was not accepted: {ordinary_failure}"
        )

    leaked_result = evaluate_failure(
        "== Optimized Loop ==\nfor (int i = 0; i < 1; i++) {}\n"
    )
    if leaked_result is None or "emitted an optimized-loop section" not in leaked_result:
        raise AssertionError(
            "failure manifest accepted a rejected command that emitted an old result"
        )

    print("[manifest-runner] OK (failed commands cannot emit optimized results)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
