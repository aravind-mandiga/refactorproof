"""Generate candidate variants for every task and transformation, logging all attempts.

Usage::

    python -m refactorproof.generate --verina-root external/verina \
        --tasks data/all_tasks.txt --out artifacts/variants --transformations T1 T2 --seed 0

Outputs
  artifacts/variants/<task_id>/<variant_id>/variant.json
  results/candidate_manifest.jsonl      one record per (task, transformation), incl. inapplicable
  results/variant_manifest.jsonl        one record per generated variant
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import List, Optional

from .transformations import get_transformations
from .verina_parser import iter_task_dirs, load_task


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--tasks", type=Path, help="file with task ids (one per line); default all")
    ap.add_argument("--out", type=Path, default=Path("artifacts/variants"))
    ap.add_argument("--results-dir", type=Path, default=Path("results"))
    ap.add_argument("--transformations", nargs="+", default=["T1", "T2"])
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args(argv)

    wanted = None
    if args.tasks:
        wanted = {ln.strip() for ln in args.tasks.read_text().splitlines() if ln.strip()}
    task_dirs = [d for d in iter_task_dirs(args.verina_root) if wanted is None or d.name in wanted]
    transformations = get_transformations(args.transformations)

    args.out.mkdir(parents=True, exist_ok=True)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    cand_path = args.results_dir / "candidate_manifest.jsonl"
    var_path = args.results_dir / "variant_manifest.jsonl"

    # merge with existing manifests so repeated runs with other transformations accumulate
    existing_c = {}
    if cand_path.exists():
        for ln in cand_path.read_text().splitlines():
            if ln.strip():
                d = json.loads(ln)
                existing_c[(d["task_id"], d["transformation"])] = d
    existing_v = {}
    if var_path.exists():
        for ln in var_path.read_text().splitlines():
            if ln.strip():
                d = json.loads(ln)
                existing_v[d["variant_id"]] = d

    # remove stale variant dirs / manifest rows of the transformations being regenerated
    import shutil

    regen_names = {t.name for t in transformations}
    for d in task_dirs:
        for old in (args.out / d.name).glob(f"{d.name}__*"):
            if old.is_dir() and any(old.name == f"{d.name}__{n}__{k}" for n in regen_names for k in range(0, 50)):
                shutil.rmtree(old)
    existing_v = {k: v for k, v in existing_v.items() if not (v["transformation"] in regen_names and v["task_id"] in {d.name for d in task_dirs})}

    n_app = n_gen = 0
    for d in task_dirs:
        tb = load_task(d)
        for t in transformations:
            ok, reason = t.applicable(tb)
            variants = t.generate(tb, args.seed) if ok else []
            rec = t.record(tb, ok, reason, variants)
            existing_c[(tb.task_id, t.name)] = rec.to_json()
            n_app += int(ok)
            for v in variants:
                # invariants at generation time
                new_tb = tb.with_block_content("code", v.transformed_code).with_block_content("code_aux", v.transformed_code_aux)
                assert new_tb.spec_hash() == tb.spec_hash(), v.variant_id
                assert new_tb.proof_hash() == tb.proof_hash(), v.variant_id
                vdir = args.out / tb.task_id / v.variant_id
                vdir.mkdir(parents=True, exist_ok=True)
                payload = v.to_json()
                payload.update(
                    {
                        "spec_hash": tb.spec_hash(),
                        "proof_hash": tb.proof_hash(),
                        "code_hash_original": tb.block("code").sha256(),
                        "code_aux_hash_original": tb.block("code_aux").sha256(),
                        "tier": rec.tier,
                        "function_name": tb.signature.name,
                        "code_loc_original": rec.code_loc_original,
                        "code_loc_refactored": rec.code_loc_refactored,
                    }
                )
                (vdir / "variant.json").write_text(json.dumps(payload, indent=1, ensure_ascii=False))
                existing_v[v.variant_id] = payload
                n_gen += 1

    with cand_path.open("w") as f:
        for k in sorted(existing_c):
            f.write(json.dumps(existing_c[k], ensure_ascii=False) + "\n")
    with var_path.open("w") as f:
        for k in sorted(existing_v):
            f.write(json.dumps(existing_v[k], ensure_ascii=False) + "\n")

    print(f"[generate] tasks={len(task_dirs)} transformations={[t.name for t in transformations]} applicable_pairs={n_app} variants={n_gen}", file=sys.stderr)
    by_t = {}
    for rec in existing_c.values():
        by_t.setdefault(rec["transformation"], [0, 0, 0])
        by_t[rec["transformation"]][0] += 1
        by_t[rec["transformation"]][1] += int(rec["applicable"])
        by_t[rec["transformation"]][2] += rec["n_variants"]
    for t, (n, a, g) in sorted(by_t.items()):
        print(f"[generate]   {t}: attempted={n} applicable={a} variants={g}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
