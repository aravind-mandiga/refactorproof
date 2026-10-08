"""Evaluate one proof artifact on the certified variants of a task (byte-fixed proof).

Shared by the proof-selection sensitivity analysis and the candidate-selection experiments: both need
to load a task's certified variants and re-check a fixed proof against each of them.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import List, Tuple

from .lean_runner import LeanRunner
from .survival import ProofArtifact, apply_proof, apply_variant, evaluate_file, same_public_header
from .transformations.base import Variant
from .verina_parser import load_task


def certified_variants(variants_root: Path, task_id: str, families: List[str]) -> List[Tuple[Variant, dict]]:
    out = []
    for vj in sorted((variants_root / task_id).glob("*/variant.json")) if (variants_root / task_id).exists() else []:
        payload = json.loads(vj.read_text())
        if payload["transformation"] not in families:
            continue
        cert_p = vj.parent / "certificate.json"
        if not cert_p.exists():
            continue
        cert = json.loads(cert_p.read_text())
        if not cert.get("certificate_valid"):
            continue
        v = Variant(**{k: payload.get(k, [] if k == "extra_levels" else None) for k in Variant.__dataclass_fields__ if k in payload or k == "extra_levels"})
        out.append((v, cert))
    return out


def evaluate_on_variants(runner: LeanRunner, verina_root: Path, task_id: str, cand: dict, variants: List[Tuple[Variant, dict]], work_dir: Path) -> List[dict]:
    """Survival of one Lean-valid candidate on the given certified variants (byte-fixed proof).  Returns
    per-variant records with proof-region diagnostics."""
    tb = load_task(verina_root / "datasets" / "verina" / task_id)
    art = ProofArtifact("model", cand["proof_text"], cand["proof_aux_text"], extra_imports="")
    tb_orig = apply_proof(tb, art).with_block_content("import", cand["imports_text"])
    recs = []
    for v, cert in variants:
        tb_eval = apply_variant(tb_orig, v)
        assert tb_eval.proof_hash() == tb_orig.proof_hash() and tb_eval.spec_hash() == tb.spec_hash() and same_public_header(tb_eval, tb)
        src = tb_eval.render()
        assert "rp_equiv" not in src and "RPRef" not in src
        out_path = work_dir / f"{v.variant_id}.lean"
        res, info = evaluate_file(runner, tb_eval, out_path)
        ok = res.ok and not info["declaration_uses_sorry"]
        outcome = "build_error" if (info["other_region_errors"] and not info["proof_region_errors"]) else ("survives" if ok else "proof_fails")
        recs.append({"variant_id": v.variant_id, "transformation": v.transformation, "severity": v.severity, "survives": outcome == "survives", "outcome": outcome, "diagnostics": info["proof_region_errors"][:3]})
    return recs
