#!/usr/bin/env bash
# Resumable download of Goedel-LM/Goedel-Prover-V2-32B (bf16) to scratch, then shard verification (exit 1 if incomplete).
set -euo pipefail
export HF_HOME=${HF_HOME:-$HOME/.cache/huggingface} HF_HUB_ENABLE_HF_TRANSFER=1
DEST=${RP_MODELS_DIR:-models}/Goedel-Prover-V2-32B
PY=${RP_VENV_VERINA:-.venv-verina}/bin/python
echo "[dl] start $(date +%T) host=$(hostname) have=$(du -sh $DEST 2>/dev/null | cut -f1)"
"$PY" - <<'PYEOF'
from huggingface_hub import snapshot_download
p = snapshot_download("Goedel-LM/Goedel-Prover-V2-32B", local_dir="${RP_MODELS_DIR:-models}/Goedel-Prover-V2-32B", max_workers=8)
print("DONE", p)
PYEOF
"$PY" - <<'PYEOF'
import json, os, sys
base = "${RP_MODELS_DIR:-models}/Goedel-Prover-V2-32B"
d = json.load(open(f"{base}/model.safetensors.index.json")); files = set(d["weight_map"].values())
missing = [f for f in files if not os.path.exists(f"{base}/{f}")]
print(f"[dl] shards expected {len(files)}, missing {len(missing)}")
sys.exit(1 if missing or not os.path.exists(f"{base}/config.json") else 0)
PYEOF
echo "[dl] verified $(date +%T) size=$(du -sh $DEST | cut -f1)"
