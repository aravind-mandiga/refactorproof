"""The supplementary analyses that need Lean: survival of every valid sample, and the
pre-registered mechanical repairs of structural failures.

Both reuse the frozen generation artifacts; neither calls a model.

    python -m refactorproof.revision_v2_lean selection_eval --workers 24
    python -m refactorproof.revision_v2_lean repairs --workers 24
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .variant_eval import certified_variants, evaluate_on_variants
from .lean_runner import LeanRunner
from .revision_v2 import ALL_MODELS, FAMILIES, PROVERS, verina_dir

SELECTION_ROOT = Path("artifacts/selection_sensitivity")
REPAIR_ROOT = Path("artifacts/mechanical_repairs")


def valid_attempts(root: Path, model: str, task: str) -> List[dict]:
    s = root / "artifacts" / "model_proofs" / model / task / "summary.json"
    if not s.exists():
        return []
    js = json.loads(s.read_text())
    out = []
    for a in sorted(js.get("attempts", []), key=lambda x: int(x.get("attempt", 0))):
        if not a.get("original_proof_valid"):
            continue
        out.append({
            "attempt": int(a["attempt"]),
            "proof_text": a.get("proof_text") or a.get("proof") or "",
            "proof_aux_text": a.get("proof_aux_text") or a.get("proof_aux") or "",
            "imports_text": a.get("imports_text") or a.get("imports") or "",
            "proof_hash": a.get("proof_hash"),
        })
    return out


# --------------------------------------------------------------------------- survival of every valid sample
def run_selection_eval(args) -> int:
    root = args.root
    runner = LeanRunner(root / "external" / "verina", timeout=300)
    jobs: List[Tuple[str, str, dict]] = []
    for m in ALL_MODELS:
        base = root / "artifacts" / "model_proofs" / m
        if not base.exists():
            continue
        for d in sorted(base.iterdir()):
            for a in valid_attempts(root, m, d.name):
                jobs.append((m, d.name, a))
    print(f"[selection] {len(jobs)} valid proof artifacts across {len(ALL_MODELS)} models", file=sys.stderr)

    def one(job):
        m, task, a = job
        outp = root / SELECTION_ROOT / m / task / f"attempt_{a['attempt']}.json"
        if outp.exists() and not args.force:
            return 0
        variants = certified_variants(root / "artifacts" / "variants", task, FAMILIES)
        if not variants:
            return 0
        recs = evaluate_on_variants(runner, root / "external" / "verina", task, a, variants,
                                    root / SELECTION_ROOT / m / task / f"lean_{a['attempt']}")
        outp.parent.mkdir(parents=True, exist_ok=True)
        outp.write_text(json.dumps({
            "model_id": m, "task_id": task, "attempt": a["attempt"], "proof_hash": a["proof_hash"],
            "proof_loc": len([l for l in a["proof_text"].splitlines() if l.strip()]),
            "proof_tokens": len(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*|[^\sA-Za-z0-9]", a["proof_text"])),
            "survival": [{k: r[k] for k in ("variant_id", "transformation", "severity", "survives", "outcome")} for r in recs],
        }, indent=1))
        return 1

    done = 0
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        for i, n in enumerate(ex.map(one, jobs), 1):
            done += n
            if i % 25 == 0:
                print(f"[selection] {i}/{len(jobs)} ({done} newly evaluated)", file=sys.stderr)
    print(f"[selection] complete: {done} newly evaluated", file=sys.stderr)
    return 0


# --------------------------------------------------------------------------- pre-registered mechanical repairs
REPAIR_TEMPLATES = {
    "unfold_add_helper": "if the proof contains `unfold <f>`, add the generated helper name to that same unfold",
    "simp_add_helper": "if the proof contains `simp [... <f> ...]`, add the generated helper name to that simp list",
    "dsimp_add_helper": "if the proof contains `dsimp [... <f> ...]`, add the generated helper name to that dsimp list",
}


def apply_repair(proof: str, fname: str, helper: str, template: str) -> Optional[str]:
    """Apply one pre-registered mechanical edit; return None when it is not syntactically applicable."""
    f = re.escape(fname)
    if template == "unfold_add_helper":
        pat = re.compile(rf"(\bunfold\b[^\n]*?\b{f}\b)")
        if not pat.search(proof):
            return None
        return pat.sub(lambda m: m.group(1) + " " + helper, proof, count=1)
    tac = "simp" if template == "simp_add_helper" else "dsimp"
    # a simp/dsimp lemma list mentioning the target function, e.g. simp [f, g] / simp only [f] / simp_all [f]
    pat = re.compile(rf"(\b{tac}(?:_all)?\b(?:\s+only)?\s*\[)([^\]\n]*\b{f}\b[^\]\n]*)(\])")
    if not pat.search(proof):
        return None
    return pat.sub(lambda m: m.group(1) + m.group(2) + ", " + helper + m.group(3), proof, count=1)


def _primary_material(root: Path):
    # (model, task) -> primary artifact; (model, task, proof_hash) -> any artifact with that exact proof hash
    prim, by_hash = {}, {}
    for line in (root / "results" / "model_proofs.jsonl").open():
        d = json.loads(line)
        mat = {"proof_text": d.get("proof_text") or d.get("proof") or "",
               "proof_aux_text": d.get("proof_aux_text") or d.get("proof_aux") or "",
               "imports_text": d.get("imports_text") or d.get("imports") or "",
               "proof_hash": d.get("proof_hash")}
        by_hash.setdefault((d["model_id"], d["task_id"], d.get("proof_hash")), mat)
        if str(d.get("is_primary")) == "True":
            prim[(d["model_id"], d["task_id"])] = mat
    return prim, by_hash


def _material_for(root: Path, r, prim, by_hash):
    # exactly the proof material that produced the recorded survival outcome, or None
    from .verina_parser import load_task
    if r["source"] == "reference":
        tb = load_task(verina_dir(root) / r["task_id"])
        return {"proof_text": tb.content("proof"), "proof_aux_text": tb.content("proof_aux"),
                "imports_text": tb.content("import"), "provenance": "VERINA task.lean proof/proof_aux/import blocks"}
    p = prim.get((r["source"], r["task_id"]))
    if p is not None and p["proof_hash"] == r["proof_hash"]:
        return {**p, "provenance": "primary row of results/model_proofs.jsonl, proof hash verified"}
    h = by_hash.get((r["source"], r["task_id"], r["proof_hash"]))
    if h is not None:
        return {**h, "provenance": "hash-matched row of results/model_proofs.jsonl"}
    return None


def run_repairs(args) -> int:
    import collections
    import pandas as pd
    root = args.root
    runner = LeanRunner(root / "external" / "verina", timeout=300)
    df = pd.read_csv(root / "results" / "survival_results.csv", low_memory=False)
    df["source"] = df.apply(lambda r: "reference" if r["proof_source"] == "reference" else r["model_id"], axis=1)
    struct = df[(df.transformation.isin(["T2_helper_extract", "T5_branch_extract"]))
                & (~df.survives.astype(bool)) & (df.source.isin(["reference"] + PROVERS))].copy()
    prim, by_hash = _primary_material(root)
    variant_meta = {}
    for vp in (root / "artifacts" / "variants").glob("*/*/variant.json"):
        v = json.loads(vp.read_text())
        variant_meta[v["variant_id"]] = v
    (root / REPAIR_ROOT).mkdir(parents=True, exist_ok=True)
    (root / REPAIR_ROOT / "preregistered_templates.json").write_text(json.dumps(REPAIR_TEMPLATES, indent=1))
    jobs, ledger = [], []
    for _, r in struct.iterrows():
        v = variant_meta.get(r["variant_id"])
        entry = {"variant_id": r["variant_id"], "task_id": r["task_id"], "source": r["source"],
                 "transformation": r["transformation"], "applicable_templates": [], "skip_reason": None}
        if v is None or not (v.get("helper_names") or []):
            entry["skip_reason"] = "no generated helper recorded"
            ledger.append(entry)
            continue
        mat = _material_for(root, r, prim, by_hash)
        if mat is None or not mat["proof_text"].strip():
            entry["skip_reason"] = "evaluated proof material not recoverable"
            ledger.append(entry)
            continue
        for tmpl in REPAIR_TEMPLATES:
            edited = apply_repair(mat["proof_text"], v["function_name"], v["helper_names"][0], tmpl)
            if edited is None or edited == mat["proof_text"]:
                continue
            entry["applicable_templates"].append(tmpl)
            jobs.append({"variant_id": r["variant_id"], "task_id": r["task_id"], "source": r["source"],
                         "transformation": r["transformation"], "template": tmpl,
                         "function_name": v["function_name"], "helper": v["helper_names"][0],
                         "proof_before": mat["proof_text"], "proof_after": edited,
                         "proof_aux_text": mat["proof_aux_text"], "imports_text": mat["imports_text"],
                         "material_provenance": mat["provenance"]})
        if not entry["applicable_templates"]:
            entry["skip_reason"] = "no pre-registered template is syntactically applicable"
        ledger.append(entry)
    (root / REPAIR_ROOT / "eligibility_ledger.json").write_text(json.dumps(ledger, indent=1))
    c = collections.Counter(e["source"] for e in ledger)
    ce = collections.Counter(e["source"] for e in ledger if e["applicable_templates"])
    print(f"[repairs] {len(ledger)} structural failures {dict(c)}; eligible {dict(ce)}; {len(jobs)} edits", file=sys.stderr)

    def compile_on_variant(j, proof_text, tag):
        variants = [x for x in certified_variants(root / "artifacts" / "variants", j["task_id"], FAMILIES)
                    if x[0].variant_id == j["variant_id"]]
        if not variants:
            return None
        cand = {"proof_text": proof_text, "proof_aux_text": j["proof_aux_text"], "imports_text": j["imports_text"]}
        recs = evaluate_on_variants(runner, root / "external" / "verina", j["task_id"], cand, variants,
                                    root / REPAIR_ROOT / "lean" / f"{j['variant_id']}__{j['source']}__{tag}")
        return recs[0] if recs else None

    def one(j):
        outp = root / REPAIR_ROOT / f"{j['variant_id']}__{j['source']}__{j['template']}.json"
        if outp.exists() and not args.force:
            return json.loads(outp.read_text())
        ctrl = compile_on_variant(j, j["proof_before"], f"unedited_{j['template']}")
        rec = compile_on_variant(j, j["proof_after"], j["template"])
        if rec is None:
            return None
        diag = rec.get("diagnostics")
        res = {**{k: j[k] for k in ("variant_id", "task_id", "source", "transformation", "template",
                                    "function_name", "helper", "material_provenance")},
               "control_unedited_fails": bool(ctrl is not None and not ctrl.get("survives")),
               "repaired": bool(rec.get("survives")), "outcome": rec.get("outcome"),
               "first_error": (str(diag[0])[:300] if isinstance(diag, list) and diag else None)}
        outp.write_text(json.dumps({**res, "proof_before": j["proof_before"], "proof_after": j["proof_after"]}, indent=1))
        return res

    results = []
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        for i, r in enumerate(ex.map(one, jobs), 1):
            if r:
                results.append(r)
            if i % 20 == 0:
                print(f"[repairs] {i}/{len(jobs)}", file=sys.stderr)
    ok = [r for r in results if r["control_unedited_fails"]]
    print(f"[repairs] control reproduced the failure for {len(ok)}/{len(results)} edits; "
          f"{sum(1 for r in ok if r['repaired'])} of those repaired", file=sys.stderr)
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("task", choices=["selection_eval", "repairs"])
    ap.add_argument("--root", type=Path, default=Path("."))
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args(argv)
    return {"selection_eval": run_selection_eval, "repairs": run_repairs}[args.task](args)


if __name__ == "__main__":
    sys.exit(main())
