#!/usr/bin/env bash
set -euo pipefail

cd /polcert

eval "$(opam env)"

make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
opam exec -- make test
opam exec -- make test-polopt-loop-suite
