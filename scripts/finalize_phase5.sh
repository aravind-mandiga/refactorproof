#!/usr/bin/env bash
# After the Phase 5 GPU jobs finish: (re)run model survival for any primary proofs not yet evaluated,
# then regenerate all CSVs, tables, figures and LaTeX number macros.
#   bash scripts/finalize_phase5.sh            # local, few workers
#   scripts/slurm_run.sh 24 120G 02:00:00 rp-finalize -- bash scripts/finalize_phase5.sh
set -euo pipefail
cd "${SLURM_SUBMIT_DIR:-$(dirname "$0")/..}"
# Serialize finalizes: concurrent runs delete/rewrite the same survival files (evaluate_models --force).
exec 9>logs/finalize.lock
echo "[finalize] waiting for lock..."; flock 9; echo "[finalize] lock acquired $(date +%T)"
export PYTHONPATH=src PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
W=${RP_WORKERS:-${SLURM_CPUS_PER_TASK:-4}}
RP=${RP_VENV:-.venv}/bin/python
echo "[finalize] GPU job states:"; sacct -u "$USER" -S "${RP_SINCE:-$(date -d '-7 days' +%Y-%m-%dT%H:%M)}" -X -o JobID,JobName%24,State,Elapsed -n 2>/dev/null | grep rp-gen || true
echo "[finalize] coverage so far:"
python3 - <<'EOF'
import json, collections
tasks = collections.defaultdict(set); valid = collections.defaultdict(set)
for ln in open("results/model_proofs.jsonl"):
    d = json.loads(ln); tasks[d["model_id"]].add(d["task_id"])
    if d.get("is_primary") and d.get("original_proof_valid"): valid[d["model_id"]].add(d["task_id"])
for m in sorted(tasks): print(f"  {m}: tasks={len(tasks[m])} with_valid_proof={len(valid[m])} coverage={len(valid[m])/len(tasks[m]):.3f}")
EOF
# 1) Re-run the Lean check on every saved attempt with the current indentation normalisation
#    (earlier generation runs checked proofs with a normaliser that misaligned tactic lines).
VENV_PY=${RP_VENV_VERINA:-.venv-verina}/bin/python
for m in $(python3 -c "import yaml; print(' '.join(yaml.safe_load(open('configs/models.yaml'))['models']))"); do
  [ -d "artifacts/model_proofs/$m" ] || continue
  PYTHONPATH=src:external/verina/src "$VENV_PY" -m refactorproof.gen_proofs --verina-root external/verina --model "$m" --recheck --lean-workers "$W"
done
# 2) Survival of primary proofs on all certified variants (force: earlier job-internal runs used stale validity)
find artifacts/variants -name 'model_*.json' -delete; find artifacts/variants -name 'model_*.lean' -delete
python -m refactorproof.evaluate_models --verina-root external/verina --variants artifacts/variants --proofs results/model_proofs.jsonl --workers "$W" --force
"$RP" -m refactorproof.analyze --results results --data data --verina-root external/verina --n-boot 10000
"$RP" -m refactorproof.make_tables --results results --out paper_artifacts
echo "[finalize] tables:"; ls paper_artifacts/tables; echo "[finalize] matched comparison:"; cat results/matched_comparison.csv 2>/dev/null | head -20 || echo "(no matched comparison yet)"
