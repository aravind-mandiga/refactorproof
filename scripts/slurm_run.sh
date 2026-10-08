#!/usr/bin/env bash
# Submit an arbitrary refactorproof command as a SLURM batch job on the cluster.
#
#   scripts/slurm_run.sh <cpus> <mem> <walltime> <job-name> -- <command...>
# e.g.
#   scripts/slurm_run.sh 32 120G 02:00:00 rp-audit -- python -m refactorproof.audit --verina-root external/verina --workers 32
#
# Logs land in logs/<job-name>-<jobid>.out. The job runs from the repo root with
# the refactorproof venv on PATH and elan on PATH.
set -euo pipefail
CPUS=$1; MEM=$2; TIME=$3; NAME=$4; shift 4
[[ "$1" == "--" ]] && shift
REPO=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$REPO/logs"
PARTITION=${RP_PARTITION:-batch}
ACCOUNT=${RP_ACCOUNT:?set RP_ACCOUNT to your SLURM account}
VENV=${RP_VENV:-.venv}
CMD="$*"
sbatch --parsable \
  --job-name="$NAME" --partition="$PARTITION" --account="$ACCOUNT" \
  --nodes=1 --ntasks=1 --cpus-per-task="$CPUS" --mem="$MEM" --time="$TIME" \
  --output="$REPO/logs/${NAME}-%j.out" --error="$REPO/logs/${NAME}-%j.out" \
  --export=ALL,PYTHONPATH="$REPO/src",PATH="$VENV/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH",LEAN_NUM_THREADS=1 \
  --chdir="$REPO" \
  --wrap="set -x; hostname; nproc; lean --version; $CMD"
