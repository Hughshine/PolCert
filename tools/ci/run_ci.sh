#!/usr/bin/env bash
set -euo pipefail

cd /polcert

eval "$(opam env)"

bash /polcert/tools/ci/check_pluto_baseline.sh
python3 /polcert/tools/tiling_routes/test_route_telemetry.py

make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
python3 /polcert/tools/tiling_routes/check_scalar_interleaved_fusion.py \
  --polcert /polcert/polcert
opam exec -- make test
opam exec -- make test-iss-pluto-suite
opam exec -- make test-iss-pluto-live-suite
opam exec -- make test-tiling-route-suites
opam exec -- make test-polopt-loop-suite
