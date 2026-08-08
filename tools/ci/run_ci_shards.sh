#!/usr/bin/env bash
set -euo pipefail

readonly image="${1:-polcert-ci:gha}"
readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly expected_shards=$'tiling-second-rejection\ntiling-second-manifest\ntiling-second-routes\ntiling-compat\ngenerated\ntiling-core\nbase'

source "$script_dir/ci_resources.sh"

readonly max_test_jobs="${CI_MAX_TEST_JOBS:-5}"
readonly test_memory_mb="${CI_TEST_MEMORY_MB_PER_JOB:-1024}"
test_jobs="$(ci_choose_jobs CI_TEST_JOBS "$max_test_jobs" "$test_memory_mb")"
readonly test_jobs
readonly log_dir="${RUNNER_TEMP:-/tmp}/polcert-ci-shards"

shard_output="$(
  docker run --rm --entrypoint bash "$image" \
    -lc 'bash /polcert/tools/ci/run_ci_shard.sh --list'
)"
readonly shard_output
if [[ -z "$shard_output" ]]; then
  printf 'CI image returned an empty shard list\n' >&2
  exit 2
fi
if [[ "$shard_output" != "$expected_shards" ]]; then
  printf 'CI image returned an unexpected shard list:\n%s\n' "$shard_output" >&2
  exit 2
fi
mapfile -t shards <<<"$shard_output"
for shard in "${shards[@]}"; do
  if ! [[ "$shard" =~ ^[a-z0-9-]+$ ]]; then
    printf 'invalid CI shard name: %q\n' "$shard" >&2
    exit 2
  fi
done

rm -rf "$log_dir"
mkdir -p "$log_dir"

printf '[ci-resources] cores=%s available_memory_mb=%s test_jobs=%s shards=%s\n' \
  "$(ci_detect_cores)" "$(ci_detect_memory_mb)" "$test_jobs" "${#shards[@]}"

run_shard() {
  local shard="$1"
  local log="$log_dir/$shard.log"
  local status="$log_dir/$shard.status"
  local started finished rc

  started="$(date +%s)"
  printf '[ci-shard] START %s\n' "$shard"
  set +e
  docker run --rm --entrypoint bash "$image" \
    -lc "bash /polcert/tools/ci/run_ci_shard.sh '$shard'" \
    >"$log" 2>&1
  rc=$?
  set -e
  finished="$(date +%s)"
  printf '%s %s\n' "$rc" "$((finished - started))" >"$status"
  printf '[ci-shard] END %s wall=%ss exit=%s\n' \
    "$shard" "$((finished - started))" "$rc"
  return "$rc"
}

active=0
for shard in "${shards[@]}"; do
  run_shard "$shard" &
  active=$((active + 1))
  if ((active >= test_jobs)); then
    wait -n || true
    active=$((active - 1))
  fi
done

while ((active > 0)); do
  wait -n || true
  active=$((active - 1))
done

failed=0
for shard in "${shards[@]}"; do
  if [[ ! -s "$log_dir/$shard.status" ]]; then
    printf '::group::CI shard %s (missing status)\n' "$shard"
    if [[ -f "$log_dir/$shard.log" ]]; then
      cat "$log_dir/$shard.log"
    fi
    printf '::endgroup::\n'
    failed=1
    continue
  fi
  read -r rc duration <"$log_dir/$shard.status"
  printf '::group::CI shard %s (wall=%ss, exit=%s)\n' "$shard" "$duration" "$rc"
  cat "$log_dir/$shard.log"
  printf '::endgroup::\n'
  if ((rc != 0)); then
    failed=1
  fi
done

if ((failed != 0)); then
  printf 'one or more CI shards failed\n' >&2
  exit 1
fi

printf 'all %s CI shards passed\n' "${#shards[@]}"
