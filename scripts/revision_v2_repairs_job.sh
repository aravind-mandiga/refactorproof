#!/usr/bin/env bash
# Mechanical repairs, with the harness that: reference proofs from VERINA source blocks, model proofs from the
# hash-verified primary artifact, and an unedited-proof control compiled for every edit.
set -euo pipefail
REPO=${SLURM_SUBMIT_DIR:-$(cd "$(dirname "$0")/.." && pwd)}; cd "$REPO"
export PYTHONPATH="$REPO/src:$REPO/external/verina/src" PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
PY=${RP_VENV_VERINA:-.venv-verina}/bin/python
W=${SLURM_CPUS_PER_TASK:-24}
echo "[repairs_v2] host=$(hostname) cpus=$W"
(cd external/verina && lake env lean --version)
"$PY" -m refactorproof.revision_v2_lean repairs --workers "$W" --force
echo "[repairs_v2] done"
