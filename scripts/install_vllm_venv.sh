#!/usr/bin/env bash
# Separate serving environment with a recent vLLM (native Qwen3 support, FP8 on Ampere). VERINA's own
# venv keeps its pinned vllm 0.8.3; the server only needs to expose an OpenAI-compatible endpoint.
set -euo pipefail
V=${RP_VENV_VLLM:-.venv-vllm}
export UV_CACHE_DIR=${UV_CACHE_DIR:-$HOME/.cache/uv}
~/.local/bin/uv venv --python 3.12 "$V"
~/.local/bin/uv pip install --python "$V/bin/python" "vllm>=0.10,<0.12" hf_transfer
"$V/bin/python" -c "import vllm, torch; print('VLLM_READY', vllm.__version__, 'torch', torch.__version__, 'cuda', torch.version.cuda)"
