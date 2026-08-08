#!/usr/bin/env bash
set -euo pipefail

readonly shard="${1:---list}"

list_shards() {
  # Keep the longest shard first so the host scheduler starts it immediately.
  printf '%s\n' \
    tiling-second-rejection \
    tiling-second-manifest \
    tiling-second-routes \
    tiling-compat \
    generated \
    tiling-core \
    base
}

if [[ "$shard" == --list ]]; then
  list_shards
  exit 0
fi

cd /polcert
eval "$(opam env --switch=polcert)"
source /polcert/tools/ci/ci_resources.sh

case "$shard" in
  base)
    ci_run_timed scalar-interleaved \
      python3 /polcert/tools/tiling_routes/check_scalar_interleaved_fusion.py \
        --polcert /polcert/polcert
    ci_run_timed legacy-tests opam exec --switch=polcert -- make test
    ci_run_timed iss-suite opam exec --switch=polcert -- make test-iss-pluto-suite
    ci_run_timed iss-live-suite opam exec --switch=polcert -- make test-iss-pluto-live-suite
    ;;
  tiling-core)
    ci_run_timed direct-routes opam exec --switch=polcert -- make test-direct-only-tiling-routes
    ci_run_timed non-second-level-routes opam exec --switch=polcert -- make test-non-second-level-tiling-routes
    ci_run_timed parallel-current opam exec --switch=polcert -- make test-parallel-current-suite
    ci_run_timed vector-current opam exec --switch=polcert -- make test-vector-current-suite
    ci_run_timed diamond-tiling opam exec --switch=polcert -- make test-diamond-tiling-suite
    ;;
  tiling-compat)
    ci_run_timed pluto-compat opam exec --switch=polcert -- make test-pluto-compat-suite
    ;;
  tiling-second-rejection)
    ci_run_timed second-level-rejection \
      opam exec --switch=polcert -- make test-second-level-tile-rejection
    ;;
  tiling-second-manifest)
    ci_run_timed second-level-manifest \
      opam exec --switch=polcert -- make test-second-level-tile-manifest
    ;;
  tiling-second-routes)
    ci_run_timed second-level-routes \
      opam exec --switch=polcert -- make test-second-level-tile-routes
    ;;
  generated)
    ci_run_timed strict-generated opam exec --switch=polcert -- make test-polopt-loop-suite
    ;;
  *)
    printf 'unknown CI shard: %s\n' "$shard" >&2
    printf 'known shards:\n' >&2
    list_shards >&2
    exit 2
    ;;
esac
