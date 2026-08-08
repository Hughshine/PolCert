#!/usr/bin/env bash
set -euo pipefail

bash /polcert/tools/ci/run_ci_build.sh

shard_output="$(bash /polcert/tools/ci/run_ci_shard.sh --list)"
readonly shard_output
if [[ -z "$shard_output" ]]; then
  printf 'empty CI shard list\n' >&2
  exit 2
fi

while IFS= read -r shard; do
  bash /polcert/tools/ci/run_ci_shard.sh "$shard"
done <<<"$shard_output"
