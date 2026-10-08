#!/usr/bin/env bash
# End-to-end smoke test on a handful of tasks (runs fine on 1 CPU; ~10 Lean compiles).
#   scripts/smoke_test.sh [task_id ...]     default: verina_basic_15 verina_basic_1
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=src PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
TASKS=${*:-verina_basic_15 verina_basic_1}
echo "[smoke] lean: $(cd external/verina && lake env lean --version)"
for t in $TASKS; do
  echo "[smoke] compiling original $t"
  ( cd external/verina && /usr/bin/time -f "  %es wall, %MKB maxrss" lake env lean "datasets/verina/$t/task.lean" )
done
ONLY=""
for t in $TASKS; do for d in artifacts/variants/$t/*/; do ONLY="$ONLY $(basename "$d")"; done; done
# shellcheck disable=SC2086
python -m refactorproof.certify --verina-root external/verina --variants artifacts/variants --workers 2 --only $ONLY --force
# shellcheck disable=SC2086
python -m refactorproof.evaluate_reference --verina-root external/verina --variants artifacts/variants --workers 2 --only $ONLY --force
echo "[smoke] certificates:"
for t in $TASKS; do for d in artifacts/variants/$t/*/; do
  python - "$d" <<'EOF'
import json, sys, pathlib
d = pathlib.Path(sys.argv[1])
c = json.loads((d / "certificate.json").read_text())
s = json.loads((d / "survival_reference.json").read_text()) if (d / "survival_reference.json").exists() else {}
print(f"  {d.name:50s} valid={c.get('certificate_valid')!s:5s} rfl={c.get('certificate_closed_by_rfl')!s:5s} level={c.get('certificate_level')} cat={c.get('certificate_failure_category')} | survival={s.get('outcome')} cat={s.get('failure_category')}")
EOF
done; done
