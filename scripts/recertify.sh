#!/usr/bin/env bash
# Re-run certification for ALL variants with the current certificate builder, then rebuild the
# reference-proof survival results from scratch (stale survival records are removed first).
#   scripts/slurm_run.sh 24 120G 03:00:00 rp-recert -- bash scripts/recertify.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=src
W=${RP_WORKERS:-${SLURM_CPUS_PER_TASK:-4}}
echo "[recert] workers=$W host=$(hostname) lean=$(cd external/verina && lake env lean --version)"
find artifacts/variants -name 'survival_reference.json' -delete
find artifacts/variants -name 'reference.lean' -delete
python -m refactorproof.certify --verina-root external/verina --variants artifacts/variants --workers "$W" --timeout 300 --force
python -m refactorproof.evaluate_reference --verina-root external/verina --variants artifacts/variants --tasks data/reference_tasks.txt --workers "$W" --timeout 300 --force
python -m refactorproof.analyze --results results --verina-root external/verina --n-boot 2000 || true
echo "[recert] done"
