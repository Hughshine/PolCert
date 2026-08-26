#!/usr/bin/env bash
set -euo pipefail

cd /polcert
eval "$(opam env --switch=polcert)"

source /polcert/tools/ci/ci_resources.sh

# Keep the fallbacks aligned with the Docker CI target. Resource detection still
# caps this by the runner's CPU quota and currently available memory.
readonly max_proof_jobs="${CI_MAX_PROOF_JOBS:-4}"
readonly proof_memory_mb="${CI_PROOF_MEMORY_MB_PER_JOB:-3072}"
proof_jobs="$(ci_choose_jobs CI_PROOF_JOBS "$max_proof_jobs" "$proof_memory_mb")"
readonly proof_jobs

printf '[ci-resources] cores=%s available_memory_mb=%s proof_jobs=%s\n' \
  "$(ci_detect_cores)" "$(ci_detect_memory_mb)" "$proof_jobs"

ci_run_timed pluto-baseline \
  bash /polcert/tools/ci/check_pluto_baseline.sh
ci_run_timed route-telemetry \
  python3 /polcert/tools/tiling_routes/test_route_telemetry.py
ci_run_timed clean make clean
ci_run_timed depend opam exec --switch=polcert -- make depend
ci_run_timed proof opam exec --switch=polcert -- make -j"$proof_jobs" proof
ci_run_timed check-admitted opam exec --switch=polcert -- make -s check-admitted
ci_run_timed extraction \
  opam exec --switch=polcert -- make -j"$proof_jobs" extraction
ci_run_timed polcert-ini opam exec --switch=polcert -- make polcert.ini
ci_run_timed extraction-depend \
  opam exec --switch=polcert -- make .depend.extr
ci_run_timed polcert \
  opam exec --switch=polcert -- make -f Makefile.extr -j"$proof_jobs" polcert
# Build polopt last.  The polcert link refreshes shared extracted OCaml objects;
# leaving polopt as the final target keeps every isolated test shard from
# rebuilding the same executable in its private container overlay.
ci_run_timed polopt \
  opam exec --switch=polcert -- make -f Makefile.extr -j"$proof_jobs" polopt
