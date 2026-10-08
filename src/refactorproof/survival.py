"""Survival evaluation: compile the *unchanged* proof against a certified refactored implementation.

For every certified variant we derive ``artifacts/variants/<task>/<variant>/<proof_source>.lean``
from the original ``task.lean`` by replacing only the ``code`` and ``code_aux`` blocks (and, for
model proofs, the proof/proof_aux/import blocks with the *same* model artifact that verified on the
original).  Specification and proof hashes are asserted unchanged before compiling.  The
equivalence certificate is never imported.

Usage::

    python -m refactorproof.evaluate_reference --verina-root external/verina \
        --variants artifacts/variants --tasks data/reference_tasks.txt --workers 8
"""

from __future__ import annotations

import argparse
import json
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .lean_runner import LeanRunner, LeanResult, contains_hole
from .transformations.base import Variant
from .verina_parser import Block, TaskBlocks, load_task


@dataclass
class ProofArtifact:
    """The proof material held fixed across original and refactored evaluation."""

    source: str  # "reference" | "model"
    proof: str
    proof_aux: str
    extra_imports: str = ""  # additional import lines from a model, appended to the solution import block
    model_id: Optional[str] = None
    generation_attempt: Optional[int] = None

    @staticmethod
    def reference(tb: TaskBlocks) -> "ProofArtifact":
        return ProofArtifact("reference", tb.content("proof"), tb.content("proof_aux"))


def apply_proof(tb: TaskBlocks, art: ProofArtifact) -> TaskBlocks:
    out = tb.with_block_content("proof", art.proof).with_block_content("proof_aux", art.proof_aux)
    if art.extra_imports.strip():
        imp = tb.content("import")
        have = {ln.strip() for ln in imp.splitlines() if ln.strip()}
        add = [ln for ln in art.extra_imports.splitlines() if ln.strip() and ln.strip() not in have]
        if add:
            new_imp = imp.rstrip("\n") + "\n" + "\n".join(ln.strip() for ln in add) + "\n"
            out = out.with_block_content("import", new_imp)
    return out


def apply_variant(tb: TaskBlocks, v: Variant) -> TaskBlocks:
    out = tb.with_block_content("code", v.transformed_code).with_block_content("code_aux", v.transformed_code_aux)
    mod = (v.metadata or {}).get("header_modifier")
    if mod:
        from .verina_parser import add_def_modifier

        out = out.with_def_header(add_def_modifier(tb.def_header(), mod))
    return out


def same_public_header(a: TaskBlocks, b: TaskBlocks) -> bool:
    """Invariant F: identical name and signature; def modifiers (e.g. noncomputable) are allowed to differ."""
    from .verina_parser import strip_def_modifiers

    return strip_def_modifiers(a.def_header()) == strip_def_modifiers(b.def_header())


def block_line_range(tb: TaskBlocks, key: str) -> Tuple[int, int]:
    """1-based inclusive line range of a block's content in the rendered file."""
    line = 1
    for s in tb.segments:
        text = s if isinstance(s, str) else s.render()
        if isinstance(s, Block) and s.key == key:
            start = line + s.start_line.count("\n")
            end = start + max(s.content.count("\n") - 1, 0) + 1  # include the end marker line
            return start, end
        line += text.count("\n")
    raise KeyError(key)


def evaluate_file(runner: LeanRunner, tb_eval: TaskBlocks, out_path: Path) -> Tuple[LeanResult, dict]:
    src = tb_eval.render()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(src, encoding="utf-8")
    res = runner.compile(out_path)
    res.save(out_path.with_suffix(".compile.json"))
    p_lo, p_hi = block_line_range(tb_eval, "proof")
    pa_lo, pa_hi = block_line_range(tb_eval, "proof_aux")
    # the theorem statement sits in the text segment just before the proof block; count it as proof region
    t_lo = pa_hi + 1
    errs = res.errors
    proof_errs = [e for e in errs if t_lo <= e.line <= p_hi or pa_lo <= e.line <= pa_hi]
    other_errs = [e for e in errs if e not in proof_errs]
    sorry_warn = any("sorry" in m.text for m in res.messages if m.severity == "warning")
    info = {
        "proof_region_errors": [e.text[:500] for e in proof_errs],
        "other_region_errors": [e.text[:500] for e in other_errs],
        "declaration_uses_sorry": sorry_warn,
        "proof_line_range": [t_lo, p_hi],
    }
    return res, info


def survival_record(tb: TaskBlocks, v: Variant, art: ProofArtifact, res: LeanResult, info: dict, original_valid: bool, cert: dict) -> dict:
    ok = res.ok and not info["declaration_uses_sorry"]
    if info["other_region_errors"] and not info["proof_region_errors"]:
        outcome = "build_error"
    elif ok:
        outcome = "survives"
    else:
        outcome = "proof_fails"
    cat = None
    if outcome == "proof_fails":
        cat = "timeout_or_heartbeat" if res.timed_out else (res.errors[0].category if res.errors else "other")
    return {
        "task_id": tb.task_id,
        "variant_id": v.variant_id,
        "transformation": v.transformation,
        "severity": v.severity,
        "equivalence_class": v.equivalence_class,
        "certificate_valid": cert.get("certificate_valid"),
        "certificate_closed_by_rfl": cert.get("certificate_closed_by_rfl"),
        "certificate_level": cert.get("certificate_level"),
        "proof_source": art.source,
        "model_id": art.model_id,
        "generation_attempt": art.generation_attempt,
        "original_proof_valid": original_valid,
        "equivalence_certified": bool(cert.get("certificate_valid")),
        "outcome": outcome,
        "survives": outcome == "survives",
        "failure_category": cat,
        "lean_exit_code": res.exit_code,
        "lean_elapsed_seconds": res.elapsed_seconds,
        "proof_region_errors": info["proof_region_errors"][:3],
        "other_region_errors": info["other_region_errors"][:3],
    }


def evaluate_reference_variant(runner: LeanRunner, verina_root: Path, vdir: Path, force: bool = False) -> Optional[dict]:
    payload = json.loads((vdir / "variant.json").read_text())
    v = Variant(**{k: payload.get(k, [] if k == "extra_levels" else None) for k in Variant.__dataclass_fields__ if k in payload or k == "extra_levels"})
    cert_path = vdir / "certificate.json"
    if not cert_path.exists():
        return None
    cert = json.loads(cert_path.read_text())
    if not cert.get("certificate_valid"):
        return None
    out_json = vdir / "survival_reference.json"
    if out_json.exists() and not force:
        return json.loads(out_json.read_text())
    tb = load_task(verina_root / "datasets" / "verina" / v.task_id)
    if not tb.has_reference_proof_text():
        return None
    art = ProofArtifact.reference(tb)
    tb_eval = apply_variant(tb, v)
    # Invariants A/B/F and no leaked certificate
    assert tb_eval.spec_hash() == tb.spec_hash() == payload["spec_hash"], v.variant_id
    assert tb_eval.proof_hash() == tb.proof_hash() == payload["proof_hash"], v.variant_id
    assert same_public_header(tb_eval, tb), v.variant_id
    src = tb_eval.render()
    assert "rp_equiv" not in src and "RPOrig" not in src and "RPRef" not in src, v.variant_id
    assert not contains_hole(tb_eval.content("code")) and not contains_hole(tb_eval.content("code_aux")), v.variant_id
    res, info = evaluate_file(runner, tb_eval, vdir / "reference.lean")
    rec = survival_record(tb, v, art, res, info, original_valid=True, cert=cert)
    rec["proof_hash"] = tb.proof_hash()
    rec["spec_hash"] = tb.spec_hash()
    out_json.write_text(json.dumps(rec, indent=1, ensure_ascii=False))
    return rec


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--variants", type=Path, default=Path("artifacts/variants"))
    ap.add_argument("--results-dir", type=Path, default=Path("results"))
    ap.add_argument("--tasks", type=Path, help="restrict to task ids (e.g. data/reference_tasks.txt)")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args(argv)

    tasks = None
    if args.tasks:
        tasks = {ln.strip() for ln in args.tasks.read_text().splitlines() if ln.strip()}
    vdirs = [vj.parent for vj in sorted(args.variants.glob("*/*/variant.json")) if tasks is None or vj.parent.parent.name in tasks]
    if args.only:
        vdirs = [d for d in vdirs if d.name in set(args.only)]
    runner = LeanRunner(args.verina_root, timeout=args.timeout)
    print(f"[evaluate_reference] {len(vdirs)} variant dirs, {args.workers} workers", file=sys.stderr)
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(evaluate_reference_variant, runner, args.verina_root, d, args.force): d for d in vdirs}
        n = 0
        for f in as_completed(futs):
            d = futs[f]
            try:
                rec = f.result()
            except Exception as e:
                rec = {"variant_id": d.name, "outcome": f"evaluator_error:{type(e).__name__}", "error": str(e)[:500]}
                (d / "survival_reference.json").write_text(json.dumps(rec, indent=1))
            if rec is None:
                continue
            n += 1
            print(f"[evaluate_reference] {n} {rec['variant_id']}: {rec.get('outcome')} cat={rec.get('failure_category')} {rec.get('lean_elapsed_seconds')}s", file=sys.stderr)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    recs = [json.loads(p.read_text()) for p in sorted(args.variants.glob("*/*/survival_reference.json"))]
    with (args.results_dir / "survival_reference.jsonl").open("w") as f:
        for r in recs:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    surv = sum(1 for r in recs if r.get("survives"))
    print(f"[evaluate_reference] records={len(recs)} survives={surv}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
