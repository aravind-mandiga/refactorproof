#!/usr/bin/env bash
# Re-evaluate only the attempt files that were quarantined (oversubscribed run or Lean timeout); the rest are skipped.
set -euo pipefail
REPO=${SLURM_SUBMIT_DIR:-$(cd "$(dirname "$0")/.." && pwd)}; cd "$REPO"
export PYTHONPATH="$REPO/src:$REPO/external/verina/src" PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
PY=${RP_VENV_VERINA:-.venv-verina}/bin/python
W=${SLURM_CPUS_PER_TASK:-24}
echo "[selection_rerun] host=$(hostname) cpus=$W"
"$PY" -m refactorproof.revision_v2_lean selection_eval --workers "$W"
echo "[selection_rerun] done"
