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
python3 tests/polopt-generated/tools/materialize_polopt_cases.py --timeout-seconds 120

python3 - <<'PY'
from pathlib import Path
root = Path('/polcert/tests/polopt-generated/cases')
status_files = sorted(root.glob('*/status.txt'))
if not status_files:
    raise SystemExit('no status files produced by strict suite')
total = len(status_files)
ok = 0
changed = 0
unchanged = 0
failed = []
for sf in status_files:
    text = sf.read_text()
    lines = dict(line.split('=', 1) for line in text.splitlines() if '=' in line)
    if lines.get('result') == 'ok':
        ok += 1
        if lines.get('changed') == 'true':
            changed += 1
        else:
            unchanged += 1
    else:
        failed.append(sf.parent.name)
print(f'STRICT_SUITE total={total} ok={ok} changed={changed} unchanged={unchanged}')
if failed:
    print('STRICT_SUITE_FAILED ' + ' '.join(failed))
    raise SystemExit(1)
PY
