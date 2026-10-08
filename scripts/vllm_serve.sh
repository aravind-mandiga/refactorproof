#!/usr/bin/env bash
# Start a vLLM OpenAI-compatible server for a local model inside the current SLURM allocation
# and wait until it answers.  Prints the base URL.  Meant to be sourced/called from a GPU job.
#
#   scripts/vllm_serve.sh <model_path> <served_name> <port> [tensor_parallel] [max_model_len]
set -euo pipefail
MODEL=$1; NAME=$2; PORT=$3; TP=${4:-1}; MAXLEN=${5:-16384}
VENV=${RP_VLLM_VENV:-${RP_VENV_VERINA:-.venv-verina}}
LOG=${RP_VLLM_LOG:-logs/vllm-${NAME}-${SLURM_JOB_ID:-local}.log}
mkdir -p "$(dirname "$LOG")"
export HF_HOME=${HF_HOME:-$HOME/.cache/huggingface}
export VLLM_LOGGING_LEVEL=${VLLM_LOGGING_LEVEL:-INFO}
"$VENV/bin/python" -m vllm.entrypoints.openai.api_server \
  --model "$MODEL" --served-model-name "$NAME" --port "$PORT" --host 0.0.0.0 \
  --tensor-parallel-size "$TP" --max-model-len "$MAXLEN" --gpu-memory-utilization 0.90 \
  --dtype bfloat16 --trust-remote-code --disable-log-requests > "$LOG" 2>&1 &
VLLM_PID=$!
echo "$VLLM_PID" > "${LOG%.log}.pid"
for i in $(seq 1 180); do
  if curl -sf "http://127.0.0.1:${PORT}/v1/models" > /dev/null 2>&1; then
    echo "http://127.0.0.1:${PORT}/v1/"
    exit 0
  fi
  if ! kill -0 "$VLLM_PID" 2>/dev/null; then
    echo "vLLM exited early; see $LOG" >&2
    tail -30 "$LOG" >&2
    exit 1
  fi
  sleep 10
done
echo "vLLM did not become ready in 30 min; see $LOG" >&2
exit 1
