#!/usr/bin/env bash
# Fetch VERINA at the pinned commit and build the exact Lean environment the benchmark was evaluated in.
#
#   bash scripts/setup_verina.sh
#
# Requires `elan` (https://github.com/leanprover/elan); the toolchain itself comes from VERINA's
# lean-toolchain file.  Mathlib is fetched from the upstream build cache, not compiled from source.
set -euo pipefail
cd "$(dirname "$0")/.."

command -v elan >/dev/null || { echo "[setup] elan not found; install it from https://github.com/leanprover/elan"; exit 2; }

read -r REPO COMMIT TOOLCHAIN <<<"$(python3 -c "
import yaml
c = yaml.safe_load(open('configs/project.yaml'))
print(c['verina']['repo'], c['verina']['commit'], c['lean']['toolchain'])")"

if [ ! -d external/verina/.git ]; then
  echo "[setup] cloning $REPO"
  git clone "$REPO" external/verina
fi
git -C external/verina fetch --quiet origin "$COMMIT" 2>/dev/null || git -C external/verina fetch --quiet origin
git -C external/verina checkout --quiet "$COMMIT"
echo "[setup] VERINA at $(git -C external/verina rev-parse --short HEAD) (pinned $COMMIT)"

python3 - <<'EOF'
import hashlib, pathlib, sys, yaml
cfg = yaml.safe_load(open("configs/project.yaml"))["lean"]
for name, key in [("lake-manifest.json", "lake_manifest_sha256"), ("lakefile.lean", "lakefile_sha256")]:
    p = pathlib.Path("external/verina") / name
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    if got != cfg[key]:
        sys.exit(f"[setup] {name} sha256 {got} does not match the pinned {cfg[key]}: the Lean environment differs")
print(f"[setup] manifest matches the pinned environment (Mathlib {cfg['mathlib_rev'][:8]}, toolchain {cfg['toolchain']})")
EOF

cd external/verina
echo "[setup] toolchain: $(cat lean-toolchain)"
lake exe cache get
lake build
lake env lean --version
echo "[setup] done; all Lean compiles in this project run as 'lake env lean' from external/verina"
