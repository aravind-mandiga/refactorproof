"""Apply each model's primary (first Lean-valid) proof, byte-for-byte, to every certified variant of its task.

Usage::

    python -m refactorproof.evaluate_models --verina-root external/verina --variants artifacts/variants \
        --proofs results/model_proofs.jsonl [--model qwen3-14b] --workers 16

Writes artifacts/variants/<task>/<variant>/model_<model_id>.lean|.json and results/survival_models.jsonl.
"""

from __future__ import annotations

import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional

from .lean_runner import LeanRunner, contains_hole
from .survival import ProofArtifact, apply_proof, apply_variant, evaluate_file, same_public_header, survival_record
from .transformations.base import Variant
from .verina_parser import load_task


def load_primary_proofs(path: Path, model: Optional[str]) -> Dict[str, Dict[str, dict]]:
    out: Dict[str, Dict[str, dict]] = {}
    for ln in path.read_text().splitlines():
        if not ln.strip():
            continue
        d = json.loads(ln)
        if not d.get("is_primary") or not d.get("original_proof_valid"):
            continue
        if model and d["model_id"] != model:
            continue
        out.setdefault(d["model_id"], {})[d["task_id"]] = d
    return out


def evaluate_one(runner: LeanRunner, verina_root: Path, vdir: Path, model_id: str, proof: dict, force: bool) -> Optional[dict]:
    out_json = vdir / f"model_{model_id}.json"
    if out_json.exists() and not force:
        return json.loads(out_json.read_text())
    payload = json.loads((vdir / "variant.json").read_text())
    v = Variant(**{k: payload.get(k, [] if k == "extra_levels" else None) for k in Variant.__dataclass_fields__ if k in payload or k == "extra_levels"})
    cert_path = vdir / "certificate.json"
    if not cert_path.exists():
        return None
    cert = json.loads(cert_path.read_text())
    if not cert.get("certificate_valid"):
        return None
    tb = load_task(verina_root / "datasets" / "verina" / v.task_id)
    art = ProofArtifact("model", proof["proof_text"], proof["proof_aux_text"], extra_imports="", model_id=model_id, generation_attempt=proof["attempt"])
    # rebuild exactly the original-validation file, then swap in the variant's code blocks
    tb_orig_eval = apply_proof(tb, art)
    tb_orig_eval = tb_orig_eval.with_block_content("import", proof["imports_text"])
    assert tb_orig_eval.proof_hash() == proof["proof_hash"], (v.variant_id, "proof hash drift")
    assert tb_orig_eval.block("import").sha256() == proof["imports_hash"], (v.variant_id, "imports hash drift")
    tb_eval = apply_variant(tb_orig_eval, v)
    assert tb_eval.proof_hash() == proof["proof_hash"] == tb_orig_eval.proof_hash()
    assert tb_eval.spec_hash() == tb.spec_hash() == payload["spec_hash"]
    assert same_public_header(tb_eval, tb)
    src = tb_eval.render()
    assert "rp_equiv" not in src and "RPOrig" not in src and "RPRef" not in src
    assert not contains_hole(tb_eval.content("proof")) and not contains_hole(tb_eval.content("proof_aux"))
    res, info = evaluate_file(runner, tb_eval, vdir / f"model_{model_id}.lean")
    rec = survival_record(tb, v, art, res, info, original_valid=True, cert=cert)
    rec.update({"proof_hash": proof["proof_hash"], "spec_hash": tb.spec_hash(), "proof_text": proof["proof_text"], "proof_aux_text": proof["proof_aux_text"], "model_family": proof.get("model_family"), "base_model": proof.get("base_model", model_id), "strategy_condition": proof.get("strategy_condition", "default")})
    out_json.write_text(json.dumps(rec, indent=1, ensure_ascii=False))
    return rec


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--variants", type=Path, default=Path("artifacts/variants"))
    ap.add_argument("--proofs", type=Path, default=Path("results/model_proofs.jsonl"))
    ap.add_argument("--results-dir", type=Path, default=Path("results"))
    ap.add_argument("--model", help="restrict to one model id")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args(argv)

    primaries = load_primary_proofs(args.proofs, args.model)
    runner = LeanRunner(args.verina_root, timeout=args.timeout)
    jobs = []
    for model_id, by_task in primaries.items():
        for task_id, proof in by_task.items():
            for vj in sorted((args.variants / task_id).glob("*/variant.json")):
                jobs.append((vj.parent, model_id, proof))
    print(f"[evaluate_models] models={list(primaries)} jobs={len(jobs)} workers={args.workers}", file=sys.stderr)
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(evaluate_one, runner, args.verina_root, d, m, p, args.force): (d, m) for d, m, p in jobs}
        n = 0
        for f in as_completed(futs):
            d, m = futs[f]
            try:
                rec = f.result()
            except Exception as e:
                rec = {"variant_id": d.name, "model_id": m, "outcome": f"evaluator_error:{type(e).__name__}", "error": str(e)[:500]}
                (d / f"model_{m}.json").write_text(json.dumps(rec, indent=1))
            if rec is None:
                continue
            n += 1
            print(f"[evaluate_models] {n} {m} {rec['variant_id']}: {rec.get('outcome')} cat={rec.get('failure_category')}", file=sys.stderr)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    recs = [json.loads(p.read_text()) for p in sorted(args.variants.glob("*/*/model_*.json"))]
    with (args.results_dir / "survival_models.jsonl").open("w") as f:
        for r in recs:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(f"[evaluate_models] records={len(recs)} survives={sum(1 for r in recs if r.get('survives'))}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
