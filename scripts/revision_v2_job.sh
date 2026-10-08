#!/usr/bin/env bash
# The Lean-heavy supplementary analyses on a CPU node: survival of every valid sample, and mechanical repairs.
set -euo pipefail
REPO=${SLURM_SUBMIT_DIR:-$(cd "$(dirname "$0")/.." && pwd)}; cd "$REPO"
export PYTHONPATH="$REPO/src:$REPO/external/verina/src" PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
PY=${RP_VENV_VERINA:-.venv-verina}/bin/python
W=${SLURM_CPUS_PER_TASK:-24}
echo "[revision_v2] host=$(hostname) cpus=$W"
(cd external/verina && lake env lean --version)
echo "[revision_v2] survival of every valid sample"
"$PY" -m refactorproof.revision_v2_lean selection_eval --workers "$W"
echo "[revision_v2] pre-registered mechanical repairs"
"$PY" -m refactorproof.revision_v2_lean repairs --workers "$W"
echo "[revision_v2] done"
