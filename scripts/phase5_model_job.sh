#!/usr/bin/env bash
# Phase 5 GPU job: serve one local model with vLLM, generate K proofs per task on the ORIGINAL
# implementations, Lean-check them, then evaluate the primary proofs on all certified variants.
#
#   sbatch --partition=$RP_GPU_PARTITION --account=$RP_ACCOUNT --gres=gpu:1 --cpus-per-task=32 --mem=200G \
#          --time=12:00:00 --job-name=rp-gen-qwen3 --output=logs/rp-gen-%j.out \
#          scripts/phase5_model_job.sh qwen3-14b
# The reported runs used one NVIDIA A100-80GB per generation job, with 32 CPU cores and 200 GB host RAM.
set -euo pipefail
# Usage: phase5_model_job.sh <model_key> [more_keys...]
#   The first key defines the served model; every key is generated+evaluated against that server
#   (Experiment B: strategy conditions of one base model share a single vLLM instance).
MODEL_KEY=$1
ALL_KEYS=("$@")
# When submitted directly with sbatch, $0 is a spooled copy of this script, so locate the repo via
# SLURM_SUBMIT_DIR (we submit with --chdir=<repo>) and fall back to the script location otherwise.
REPO=${RP_REPO:-${SLURM_SUBMIT_DIR:-$(cd "$(dirname "$0")/.." && pwd)}}
cd "$REPO"
[ -f pyproject.toml ] || { echo "[phase5] not a refactorproof checkout: $REPO"; exit 2; }
export PYTHONPATH="$REPO/src:$REPO/external/verina/src"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
export HF_HOME=${HF_HOME:-$HOME/.cache/huggingface}
VENV=${RP_VENV_VERINA:-.venv-verina}
PY="$VENV/bin/python"
mkdir -p logs

cfg() { "$PY" - "$MODEL_KEY" "$1" <<'EOF'
import sys, yaml
m = yaml.safe_load(open("configs/models.yaml"))["models"][sys.argv[1]]
keys = sys.argv[2].split(".")
v = m
for k in keys: v = v[k]
print(v)
EOF
}
MODEL_PATH=$(cfg model_path); SERVED=$(cfg served_model_name); TP=$(cfg vllm.tensor_parallel); MAXLEN=$(cfg vllm.max_model_len); EXTRA=$(cfg vllm.extra_args)
SERVE_PY=$(cfg vllm.python 2>/dev/null || true); [ -n "$SERVE_PY" ] && [ -x "$SERVE_PY" ] || SERVE_PY="$PY"   # optional separate serving env (e.g. $RP_VENV_VLLM/bin/python)
echo "[phase5] serving python: $SERVE_PY ($("$SERVE_PY" -c "import vllm; print(vllm.__version__)" 2>/dev/null))"
PORT=${RP_PORT:-8000}
echo "[phase5] model=$MODEL_KEY path=$MODEL_PATH served=$SERVED tp=$TP port=$PORT host=$(hostname) gpus=${CUDA_VISIBLE_DEVICES:-?}"
nvidia-smi -L || true
(cd external/verina && lake env lean --version) || { echo "[phase5] Lean environment broken"; exit 3; }

LOG=logs/vllm-${MODEL_KEY}-${SLURM_JOB_ID:-local}.log
# shellcheck disable=SC2086
"$SERVE_PY" -m vllm.entrypoints.openai.api_server --model "$MODEL_PATH" --served-model-name "$SERVED" \
  --port "$PORT" --host 127.0.0.1 --tensor-parallel-size "$TP" --max-model-len "$MAXLEN" \
  --gpu-memory-utilization 0.90 --dtype bfloat16 --trust-remote-code --disable-log-requests $EXTRA > "$LOG" 2>&1 &
VLLM_PID=$!
trap 'kill $VLLM_PID 2>/dev/null || true' EXIT
for i in $(seq 1 240); do
  curl -sf "http://127.0.0.1:${PORT}/v1/models" > /dev/null 2>&1 && break
  kill -0 "$VLLM_PID" 2>/dev/null || { echo "[phase5] vLLM died"; tail -40 "$LOG"; exit 1; }
  sleep 10
done
curl -sf "http://127.0.0.1:${PORT}/v1/models" > /dev/null || { echo "[phase5] vLLM not ready"; tail -40 "$LOG"; exit 1; }
echo "[phase5] vLLM ready"

W=${SLURM_CPUS_PER_TASK:-8}
for KEY in "${ALL_KEYS[@]}"; do
  echo "[phase5] generating for $KEY"
  "$PY" -m refactorproof.gen_proofs --verina-root external/verina --models-config configs/models.yaml \
    --model "$KEY" --api-base "http://127.0.0.1:${PORT}/v1/" --tasks data/all_tasks.txt \
    --concurrency 32 --task-concurrency 16 --lean-workers "$W" ${RP_GEN_EXTRA:-}
done

kill $VLLM_PID 2>/dev/null || true
trap - EXIT

for KEY in "${ALL_KEYS[@]}"; do
  "$PY" -m refactorproof.evaluate_models --verina-root external/verina --variants artifacts/variants \
    --proofs results/model_proofs.jsonl --model "$KEY" --workers "$W"
  echo "[phase5] done $KEY"
done
