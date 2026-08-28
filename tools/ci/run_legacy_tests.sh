#!/usr/bin/env bash
set -euo pipefail

readonly log="${RUNNER_TEMP:-/tmp}/polcert-legacy-tests.log"

if opam exec --switch=polcert -- make test >"$log" 2>&1; then
  awk '/^\[legacy\// || /^\[typed-c-pipeline\]/ { print }' "$log"
  printf '[legacy-ci] PASS expected=all-legacy-suites actual=all-passed interpretation=verbose-Pluto-traces-suppressed-full-log=%s\n' "$log"
  exit 0
fi

printf '[legacy-ci] FAIL expected=all-legacy-suites actual=failure interpretation=full-log-follows\n' >&2
cat "$log" >&2
exit 1
