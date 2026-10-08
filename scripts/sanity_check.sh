#!/usr/bin/env bash
# Fast invariant checks (no Lean): parser round trip, hash invariants, transformation shapes,
# certificate structure, plus environment pin verification against configs/project.yaml.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=src
python - <<'EOF'
import hashlib, subprocess, yaml, pathlib, sys
cfg = yaml.safe_load(open("configs/project.yaml"))
root = pathlib.Path("external/verina")
commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"]).decode().strip()
manifest = hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest()
toolchain = (root / "lean-toolchain").read_text().strip()
ok = True
for name, got, want in [("verina commit", commit, cfg["verina"]["commit"]), ("lake-manifest sha256", manifest, cfg["lean"]["lake_manifest_sha256"]), ("lean toolchain", toolchain, cfg["lean"]["toolchain"])]:
    flag = "OK " if got == want else "MISMATCH"
    ok &= got == want
    print(f"[sanity] {flag} {name}: {got}")
sys.exit(0 if ok else 1)
EOF
python -m pytest tests -q
