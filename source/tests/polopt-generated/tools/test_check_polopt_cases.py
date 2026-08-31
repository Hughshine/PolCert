#!/usr/bin/env python3
from __future__ import annotations

import check_polopt_cases


def main() -> int:
    required_changed = {"changed"}
    required_unchanged = {"unchanged"}
    required_tiled = {"changed"}

    assert not check_polopt_cases.required_effect_failures(
        "changed",
        changed=True,
        nontrivial_changed=True,
        tiled=True,
        require_nontrivial_changed=required_changed,
        require_unchanged=required_unchanged,
        require_tiled_cases=required_tiled,
    )
    assert not check_polopt_cases.required_effect_failures(
        "unchanged",
        changed=False,
        nontrivial_changed=False,
        tiled=False,
        require_nontrivial_changed=required_changed,
        require_unchanged=required_unchanged,
        require_tiled_cases=required_tiled,
    )
    failures = check_polopt_cases.required_effect_failures(
        "changed",
        changed=True,
        nontrivial_changed=False,
        tiled=False,
        require_nontrivial_changed=required_changed,
        require_unchanged=required_unchanged,
        require_tiled_cases=required_tiled,
    )
    assert failures == [
        "expected a nontrivial optimized-loop change",
        "expected explicit tiled bounds",
    ]
    failures = check_polopt_cases.required_effect_failures(
        "unchanged",
        changed=True,
        nontrivial_changed=True,
        tiled=False,
        require_nontrivial_changed=required_changed,
        require_unchanged=required_unchanged,
        require_tiled_cases=required_tiled,
    )
    assert failures == ["expected the optimized loop to remain unchanged"]
    print(
        "[strict-effect-unit] PASS expected=reject-missing-effects actual=rejected "
        "interpretation=per-case effect contracts fail closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
