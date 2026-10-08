#!/usr/bin/env bash
# One GPU job: serve + generate + evaluate for the given model keys, then run the finalize step
# (recheck all models, survival, analysis, tables) on the same allocation. Keeps the queue small.
set -euo pipefail
REPO=${SLURM_SUBMIT_DIR:-$(cd "$(dirname "$0")/.." && pwd)}; cd "$REPO"
bash scripts/phase5_model_job.sh "$@"
RP_WORKERS=${SLURM_CPUS_PER_TASK:-8} bash scripts/finalize_phase5.sh
