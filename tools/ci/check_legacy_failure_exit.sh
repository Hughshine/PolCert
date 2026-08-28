#!/usr/bin/env bash
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
tmp="$(mktemp -d -t polcert-legacy-failure-XXXXXX)"
readonly tmp
trap 'rm -rf "$tmp"' EXIT

expect_failure() {
  local name="$1"
  local expected_status="$2"
  shift 2
  local log="$tmp/$name.log"
  local status
  set +e
  "$@" >"$log" 2>&1
  status=$?
  set -e
  if [[ "$status" -ne "$expected_status" ]]; then
    printf '[legacy-failure-gate] FAIL case=%s expected=exit:%s actual=exit:%s interpretation=failure-did-not-match-the-declared-rejection-class\n' \
      "$name" "$expected_status" "$status" >&2
    cat "$log" >&2
    return 1
  fi
  printf '[legacy-failure-gate] PASS case=%s expected=exit:%s actual=exit:%s interpretation=test-binary-propagated-the-declared-failure\n' \
    "$name" "$expected_status" "$status"
}

run_self_test() {
  expect_failure exact-exit 7 bash -c 'exit 7' >/dev/null
  if expect_failure wrong-exit 7 bash -c 'exit 6' >/dev/null 2>&1; then
    printf '[legacy-failure-gate-unit] FAIL expected=mismatched-exit-rejected actual=accepted\n' >&2
    return 1
  fi
  if expect_failure zero-exit 7 bash -c 'exit 0' >/dev/null 2>&1; then
    printf '[legacy-failure-gate-unit] FAIL expected=zero-exit-rejected actual=accepted\n' >&2
    return 1
  fi
  if expect_failure missing-command 7 "$tmp/does-not-exist" >/dev/null 2>&1; then
    printf '[legacy-failure-gate-unit] FAIL expected=missing-command-rejected actual=accepted\n' >&2
    return 1
  fi
  printf '[legacy-failure-gate-unit] PASS expected=exact-exit-accepted,mismatch-zero-and-missing-rejected actual=exact-exit-accepted,mismatch-zero-and-missing-rejected interpretation=failure-gate-rejects-unrelated-nonzero-statuses\n'
}

if [[ "${1:-}" == "--self-test" ]]; then
  run_self_test
  exit 0
fi

for binary in \
  "$root/tests/readscop/test" \
  "$root/tests/pluto-all/test" \
  "$root/tests/pluto/test"; do
  if [[ ! -x "$binary" ]]; then
    printf '[legacy-failure-gate] FAIL expected=executable:%s actual=missing-or-not-executable interpretation=the-rejection-test-did-not-run\n' \
      "$binary" >&2
    exit 2
  fi
done

expect_failure readscop-missing-input 2 \
  "$root/tests/readscop/test" "$tmp/missing.scop"

mkdir -p "$tmp/corpus/a/b"
expect_failure pluto-all-missing-corpus 1 \
  bash -c 'cd "$1" && "$2"' _ \
    "$tmp/corpus/a/b" "$root/tests/pluto-all/test"

expect_failure pluto-missing-config 2 \
  bash -c 'cd "$1/tests/pluto" && COMPCERT_CONFIG="$2/missing.ini" ./test' _ \
    "$root" "$tmp"

printf '[legacy-failure-gate] PASS expected=exit-codes:2,1,2 actual=exit-codes:2,1,2 interpretation=representative-legacy-failures-return-their-declared-statuses\n'
