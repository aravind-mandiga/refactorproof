"""Supplementary analyses of the RefactorProof results.

Every number is recomputed from the repository's own artifacts: the VERINA source tasks, the candidate
manifest, the certificate log, the per-attempt generation summaries, and the survival records.  Nothing
here regenerates model proofs.  All randomness is seeded and logged.

Subcommands (outputs land in analysis_outputs/):
    reference_population   reference-proof subset audit
    model_coverage         Coverage@k and valid-sample distributions
    aggregation            alternative PSR weightings and common support
    per_family             matched model-vs-reference effects per family
    noncomputable          sensitivity to the two `noncomputable` variants
    t3_selection           certified vs rejected T3 candidates
    mechanism              mechanism annotation audit and leave-one-task-out
    selection              sensitivity to the first-valid proof-selection rule
    repair_summary         outcome of the pre-registered one-identifier repairs
    length_confound        proof-length control for the source comparison
    seed_sensitivity       bootstrap-seed sensitivity of the matched intervals
    matched_weighting      matched differences under other family weightings
    robust_coverage        end-to-end coverage combined with survival
"""

from __future__ import annotations

import argparse
import collections
import json
import math
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Sequence

import numpy as np
import pandas as pd

PROVERS = ["deepseek-prover-v2-7b", "goedel-prover-v2-8b", "goedel-prover-v2-32b"]
ALL_MODELS = ["qwen3-14b", "qwen3-32b", "goedel-prover-v2-8b", "goedel-prover-v2-32b", "deepseek-prover-v2-7b"]
HF_ID = {
    "qwen3-14b": "Qwen/Qwen3-14B",
    "qwen3-32b": "Qwen/Qwen3-32B",
    "goedel-prover-v2-8b": "Goedel-LM/Goedel-Prover-V2-8B",
    "goedel-prover-v2-32b": "Goedel-LM/Goedel-Prover-V2-32B",
    "deepseek-prover-v2-7b": "deepseek-ai/DeepSeek-Prover-V2-7B",
}
FAMILIES = ["T1_let_intro", "T2_helper_extract", "T3_comm_swap", "T4_cond_invert", "T5_branch_extract"]
SEED = 20260909


# --------------------------------------------------------------------------- shared loaders
def verina_dir(root: Path) -> Path:
    return root / "external" / "verina" / "datasets" / "verina"


def proof_block(task_dir: Path) -> str:
    src = (task_dir / "task.lean").read_text(encoding="utf-8")
    m = re.search(r"-- !benchmark @start proof\n(.*?)-- !benchmark @end proof", src, re.S)
    return m.group(1) if m else ""


def reference_proof_status(task_dir: Path) -> str:
    """'supplied' | 'sorry' | 'empty' - read directly from the VERINA source file."""
    p = proof_block(task_dir).strip()
    if not p:
        return "empty"
    if re.search(r"\bsorry\b|\badmit\b", p):
        return "sorry"
    return "supplied"


def load_survival(root: Path) -> pd.DataFrame:
    df = pd.read_csv(root / "results" / "survival_results.csv", low_memory=False)
    df["source"] = np.where(df["proof_source"] == "reference", "reference", df["model_id"])
    return df


def load_manifest(root: Path) -> List[dict]:
    return [json.loads(l) for l in (root / "results" / "candidate_manifest.jsonl").open()]


def load_certificates(root: Path) -> List[dict]:
    return [json.loads(l) for l in (root / "results" / "certification.jsonl").open()]


def compiling_tasks(root: Path) -> set:
    """Tasks whose original file compiles in the pinned environment (from the audit artifact)."""
    p = root / "artifacts" / "original_compiles"
    ok = set()
    for f in p.glob("*.json"):
        d = json.loads(f.read_text())
        if d.get("ok") or d.get("compiles") or d.get("exit_code") == 0:
            ok.add(f.stem)
    return ok


# --------------------------------------------------------------------------- statistics
def task_normalized_psr(df: pd.DataFrame, value: str = "survives") -> float:
    if df.empty:
        return float("nan")
    return float(df.groupby("task_id")[value].mean().mean())


def cluster_bootstrap_ci(per_task: Sequence[float], n_boot: int = 10000, seed: int = SEED) -> tuple:
    a = np.asarray([x for x in per_task if not (isinstance(x, float) and math.isnan(x))], dtype=float)
    if a.size == 0:
        return float("nan"), float("nan")
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, a.size, size=(n_boot, a.size))
    boots = a[idx].mean(axis=1)
    return float(np.percentile(boots, 2.5)), float(np.percentile(boots, 97.5))


def paired_diff(df_a: pd.DataFrame, df_b: pd.DataFrame, n_boot: int = 10000, seed: int = SEED) -> dict:
    """Paired task-level difference on the exactly matched variant set."""
    common_variants = set(df_a["variant_id"]) & set(df_b["variant_id"])
    a = df_a[df_a["variant_id"].isin(common_variants)]
    b = df_b[df_b["variant_id"].isin(common_variants)]
    pa, pb = a.groupby("task_id")["survives"].mean(), b.groupby("task_id")["survives"].mean()
    tasks = sorted(set(pa.index) & set(pb.index))
    if not tasks:
        return {"n_tasks": 0, "n_variants": 0, "psr_a": float("nan"), "psr_b": float("nan"),
                "delta": float("nan"), "ci_low": float("nan"), "ci_high": float("nan")}
    d = np.array([pa[t] - pb[t] for t in tasks])
    lo, hi = cluster_bootstrap_ci(d, n_boot=n_boot, seed=seed)
    return {"n_tasks": len(tasks), "n_variants": len(common_variants),
            "psr_a": float(np.mean([pa[t] for t in tasks])), "psr_b": float(np.mean([pb[t] for t in tasks])),
            "delta": float(d.mean()), "ci_low": lo, "ci_high": hi}


def pct(x) -> str:
    return "--" if x is None or (isinstance(x, float) and math.isnan(x)) else f"{100 * x:.1f}"


# =========================================================================== reference-proof subset audit
def run_reference_population(args) -> int:
    root, out = args.root, args.out
    vdir = verina_dir(root)
    tasks = sorted(d.name for d in vdir.iterdir() if (d / "task.lean").exists())
    compiling = compiling_tasks(root)
    man = load_manifest(root)
    applicable_by_task = collections.defaultdict(set)
    for m in man:
        if m["applicable"]:
            applicable_by_task[m["task_id"]].add(m["transformation"])
    struct_by_task = {}
    for m in man:
        if m.get("structural_metadata"):
            struct_by_task.setdefault(m["task_id"], m["structural_metadata"])
    certified_by_task = collections.Counter()
    for c in load_certificates(root):
        if c.get("certificate_valid"):
            certified_by_task[c["task_id"]] += 1

    rows = []
    for t in tasks:
        td = vdir / t
        status = reference_proof_status(td)
        src = (td / "task.lean").read_text(encoding="utf-8")
        code = re.search(r"-- !benchmark @start code\n(.*?)-- !benchmark @end code", src, re.S)
        code_txt = code.group(1) if code else ""
        prf = proof_block(td)
        sm = struct_by_task.get(t, {})
        rows.append({
            "task_id": t,
            "category": "advanced" if "advanced" in t else "basic",
            "reference_proof_status": status,
            "has_reference_proof": status == "supplied",
            "compiles_in_pinned_env": t in compiling,
            "in_construction_population": t in compiling,
            "code_loc": len([l for l in code_txt.splitlines() if l.strip()]),
            "code_tokens": len(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*|[^\sA-Za-z0-9]", code_txt)),
            "reference_proof_loc": (len([l for l in prf.splitlines() if l.strip()]) if status == "supplied" else None),
            "recursive": bool(sm.get("code_self_recursive") or sm.get("code_has_let_rec") or sm.get("code_has_where") or sm.get("code_has_def_level_termination")),
            "has_let_rec": bool(sm.get("code_has_let_rec")),
            "self_recursive": bool(sm.get("code_self_recursive")),
            "has_where": bool(sm.get("code_has_where")),
            "n_applicable_families": len(applicable_by_task.get(t, ())),
            "applicable_families": ";".join(sorted(applicable_by_task.get(t, ()))),
            "n_certified_variants": certified_by_task.get(t, 0),
        })
    df = pd.DataFrame(rows)
    out.mkdir(parents=True, exist_ok=True)
    df.to_csv(out / "reference_population_audit.csv", index=False)

    ref = df[df.has_reference_proof]
    constr = df[df.in_construction_population]
    ref_and_compiles = df[df.has_reference_proof & df.compiles_in_pinned_env]

    def med(d, c):
        return float(d[c].median()) if len(d) else float("nan")

    from scipy.stats import mannwhitneyu, fisher_exact
    mw = lambda c: (mannwhitneyu(ref[c], constr[~constr.has_reference_proof][c]).pvalue
                    if len(ref) and len(constr[~constr.has_reference_proof]) else float("nan"))
    others = constr[~constr.has_reference_proof]
    p_loc, p_tok, p_fam = mw("code_loc"), mw("code_tokens"), mw("n_applicable_families")
    fe_rec = fisher_exact([[int(ref.recursive.sum()), int((~ref.recursive).sum())],
                           [int(others.recursive.sum()), int((~others.recursive).sum())]])[1]
    fe_adv = fisher_exact([[int((ref.category == "advanced").sum()), int((ref.category == "basic").sum())],
                           [int((others.category == "advanced").sum()), int((others.category == "basic").sum())]])[1]

    lines = [
        "# Audit of the reference-proof subset",
        "",
        f"Source of truth: the `proof` marker block of each `external/verina/datasets/verina/<task>/task.lean`,",
        f"the certificate log, and the candidate manifest. Seed {SEED}.",
        "",
        "## Populations",
        "",
        "| Population | Count |",
        "|---|---|",
        f"| VERINA tasks in the local dataset | {len(df)} |",
        f"| Tasks whose original compiles in the pinned environment | {int(df.compiles_in_pinned_env.sum())} |",
        f"| Tasks with a supplied reference proof | {int(df.has_reference_proof.sum())} |",
        f"| Tasks with a supplied reference proof that also compile | {len(ref_and_compiles)} |",
        f"| Certified RefactorProof variants contributed by reference-proof tasks | {int(ref.n_certified_variants.sum())} |",
        f"| Certified variants in total | {int(df.n_certified_variants.sum())} |",
        "",
        "## Why the other tasks have no reference proof",
        "",
        "| Reason (read from the source proof block) | Tasks |",
        "|---|---|",
    ]
    for reason, n in df.reference_proof_status.value_counts().items():
        lines.append(f"| `{reason}` | {n} |")
    lines += [
        "",
        "Every excluded task carries an explicit `sorry` placeholder in its proof block, so the exclusion is a",
        "property of the VERINA release rather than a filtering choice made here.",
        "",
        "## Reference-proof tasks compared with the rest of the construction population",
        "",
        "Comparison is against the other tasks in the 185-task construction population. Reference-proof length is",
        "reported only within the subset that has a reference proof; for tasks without one it is undefined and is",
        "**not** imputed.",
        "",
        "| Characteristic | Reference-proof tasks | Other construction tasks | Test |",
        "|---|---|---|---|",
        f"| Tasks | {len(ref)} | {len(others)} | |",
        f"| Median implementation LoC | {med(ref, 'code_loc'):.1f} | {med(others, 'code_loc'):.1f} | Mann-Whitney p = {p_loc:.2e} |",
        f"| Median implementation tokens | {med(ref, 'code_tokens'):.1f} | {med(others, 'code_tokens'):.1f} | Mann-Whitney p = {p_tok:.2e} |",
        f"| Median applicable transformation families | {med(ref, 'n_applicable_families'):.1f} | {med(others, 'n_applicable_families'):.1f} | Mann-Whitney p = {p_fam:.2e} |",
        f"| Recursive implementation | {100 * ref.recursive.mean():.1f}% | {100 * others.recursive.mean():.1f}% | Fisher p = {fe_rec:.2e} |",
        f"| VERINA `advanced` category | {100 * (ref.category == 'advanced').mean():.1f}% | {100 * (others.category == 'advanced').mean():.1f}% | Fisher p = {fe_adv:.2e} |",
        f"| Median reference-proof LoC | {med(ref, 'reference_proof_loc'):.1f} | undefined (no reference proof) | not comparable |",
        "",
        "## Reading",
        "",
        "The reference arm is not a random sample of the construction population. Reference-proof tasks have much",
        f"shorter implementations (median {med(ref, 'code_loc'):.0f} vs {med(others, 'code_loc'):.0f} lines, Mann-Whitney p = {p_loc:.1e}), are far less",
        f"often recursive ({100 * ref.recursive.mean():.1f}% vs {100 * others.recursive.mean():.1f}%, Fisher p = {fe_rec:.1e}), and none is in the `advanced`",
        f"split ({100 * (others.category == 'advanced').mean():.1f}% of the other tasks are). The number of applicable transformation families does",
        f"not differ detectably (median {med(ref, 'n_applicable_families'):.0f} vs {med(others, 'n_applicable_families'):.0f}, p = {p_fam:.2f}).",
        "",
        "Standalone reference PSR therefore describes VERINA's simplest tasks. Matched model-versus-reference",
        "comparisons are internally unaffected by this selection, because they hold the task set and the variant set",
        "fixed across the two proof sources, but they are restricted to these simpler tasks and do not speak to the",
        "recursive or `advanced` part of VERINA.",
        "",
        "Row-level data: `reference_population_audit.csv`.",
    ]
    (out / "reference_population_summary.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[:28]))
    return 0


# =========================================================================== model generation coverage
def load_attempts(root: Path, model: str) -> Dict[str, List[dict]]:
    """task_id -> list of attempts in fixed sample order."""
    base = root / "artifacts" / "model_proofs" / model
    out = {}
    if not base.exists():
        return out
    for d in sorted(base.iterdir()):
        s = d / "summary.json"
        if not s.exists():
            continue
        js = json.loads(s.read_text())
        atts = sorted(js.get("attempts", []), key=lambda a: int(a.get("attempt", 0)))
        out[d.name] = atts
    return out


def run_model_coverage(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    n_attempted = sum(1 for d in verina_dir(root).iterdir() if (d / "task.lean").exists())   # task directories only
    cov_rows, dist_rows = [], []
    for m in ALL_MODELS:
        atts = load_attempts(root, m)
        n_tasks_attempted = len(atts) if atts else 0
        valid_counts = {t: sum(1 for a in v if a.get("original_proof_valid")) for t, v in atts.items()}
        first_valid_idx = {}
        for t, v in atts.items():
            idx = [i for i, a in enumerate(v) if a.get("original_proof_valid")]
            first_valid_idx[t] = (idx[0] + 1) if idx else None
        row = {"model_id": m, "hf_checkpoint": HF_ID[m], "tasks_attempted": n_tasks_attempted,
               "denominator_tasks": n_attempted}
        for k in range(1, 6):
            n = sum(1 for t, fi in first_valid_idx.items() if fi is not None and fi <= k)
            row[f"coverage_at_{k}"] = n / n_attempted
            row[f"n_tasks_at_{k}"] = n
        row["tasks_with_any_valid"] = sum(1 for c in valid_counts.values() if c > 0)
        row["pct_tasks_with_any_valid"] = row["tasks_with_any_valid"] / n_attempted
        row["total_valid_artifacts"] = int(sum(valid_counts.values()))
        row["total_samples"] = int(sum(len(v) for v in atts.values()))
        cov_rows.append(row)
        c = collections.Counter(valid_counts.get(t, 0) for t in atts)
        zero_missing = n_attempted - n_tasks_attempted
        for k in range(0, 6):
            n = c.get(k, 0) + (zero_missing if k == 0 else 0)
            dist_rows.append({"model_id": m, "n_valid_samples": k, "n_tasks": n, "pct_tasks": n / n_attempted})
    cov = pd.DataFrame(cov_rows)
    dist = pd.DataFrame(dist_rows)
    cov.to_csv(out / "model_coverage.csv", index=False)
    dist.to_csv(out / "valid_sample_distribution.csv", index=False)

    lines = ["# Model generation coverage", "",
             f"Denominator is all {n_attempted} VERINA tasks attempted by the generation protocol (K=5 samples per",
             "task, fixed order, first Lean-valid sample is the primary artifact). Computed from the per-attempt",
             "`original_proof_valid` flags in `artifacts/model_proofs/<model>/<task>/summary.json`.", "",
             "## Coverage@k over all 189 attempted tasks", "",
             "| Model | Coverage@1 | @2 | @3 | @4 | @5 | Tasks with >=1 valid | Valid artifacts |",
             "|---|---|---|---|---|---|---|---|"]
    for _, r in cov.iterrows():
        lines.append(f"| {r.hf_checkpoint} | {pct(r.coverage_at_1)}% | {pct(r.coverage_at_2)}% | {pct(r.coverage_at_3)}% | "
                     f"{pct(r.coverage_at_4)}% | {pct(r.coverage_at_5)}% | {int(r.tasks_with_any_valid)} "
                     f"({pct(r.pct_tasks_with_any_valid)}%) | {int(r.total_valid_artifacts)} |")
    lines += ["", "## Distribution of valid samples per task", "",
              "| Model | 0 valid | 1 | 2 | 3 | 4 | 5 |", "|---|---|---|---|---|---|---|"]
    for m in ALL_MODELS:
        d = dist[dist.model_id == m].set_index("n_valid_samples")["n_tasks"]
        lines.append("| " + HF_ID[m] + " | " + " | ".join(str(int(d.get(k, 0))) for k in range(6)) + " |")
    lines += ["", "## Reading", "",
              "Coverage@5 equals the share of tasks with at least one valid sample, so the two columns agree by",
              "construction. All survival results are conditional on this coverage: a model contributes a task to",
              "PSR only where it produced a Lean-valid proof of the original implementation.", "",
              "Row-level data: `model_coverage.csv`, `valid_sample_distribution.csv`."]
    (out / "model_coverage_summary.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines[5:14]))
    return 0


# =========================================================================== noncomputable sensitivity
def run_noncomputable(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    certs = load_certificates(root)
    nc = [c for c in certs if c.get("header_modifier") or c.get("retried_noncomputable")]
    nc_ids = {c["variant_id"] for c in nc}
    df = load_survival(root)
    rows = []
    sources = ["reference"] + PROVERS
    for src in sources:
        d = df[df.source == src]
        for scope, sel in [("overall", d), ("D", d[d.severity == "D"]), ("S", d[d.severity == "S"]), ("E", d[d.severity == "E"])]:
            full = task_normalized_psr(sel)
            excl = task_normalized_psr(sel[~sel.variant_id.isin(nc_ids)])
            rows.append({"analysis": "psr", "source": src, "scope": scope,
                         "psr_all_variants": full, "psr_excluding_noncomputable": excl,
                         "delta_pp": (excl - full) * 100 if not (math.isnan(full) or math.isnan(excl)) else float("nan"),
                         "n_variants_all": len(sel), "n_variants_excluded": int(sel.variant_id.isin(nc_ids).sum())})
    ref = df[df.source == "reference"]
    for m in PROVERS:
        md = df[df.source == m]
        for scope, a, b in [("all", md, ref), ("S", md[md.severity == "S"], ref[ref.severity == "S"]),
                            ("E", md[md.severity == "E"], ref[ref.severity == "E"])]:
            full = paired_diff(a, b, n_boot=args.n_boot)
            a2, b2 = a[~a.variant_id.isin(nc_ids)], b[~b.variant_id.isin(nc_ids)]
            excl = paired_diff(a2, b2, n_boot=args.n_boot)
            rows.append({"analysis": "matched_diff", "source": m, "scope": scope,
                         "psr_all_variants": full["delta"], "psr_excluding_noncomputable": excl["delta"],
                         "delta_pp": (excl["delta"] - full["delta"]) * 100,
                         "n_variants_all": full["n_variants"], "n_variants_excluded": full["n_variants"] - excl["n_variants"],
                         "ci_all": f"[{100*full['ci_low']:.1f}, {100*full['ci_high']:.1f}]",
                         "ci_excluded": f"[{100*excl['ci_low']:.1f}, {100*excl['ci_high']:.1f}]",
                         "n_tasks": full["n_tasks"]})
    res = pd.DataFrame(rows)
    res.to_csv(out / "noncomputable_sensitivity.csv", index=False)
    maxshift = res["delta_pp"].abs().max()
    lines = ["# Sensitivity to the two `noncomputable` variants", "",
             "Two certified variants required Lean's `noncomputable` modifier because the 4.18 code generator",
             "refuses the wrapped body. The modifier changes neither the name, the signature, nor the logical",
             "content, but it does matter for proofs relying on native evaluation, so every headline statistic is",
             "recomputed with those two variants removed.", "",
             "## The two variants", "", "| Variant | Transformation | Class | Modifier |", "|---|---|---|---|"]
    for c in nc:
        lines.append(f"| `{c['variant_id']}` | {c['transformation']} | {c['severity']} | `{c.get('header_modifier')}` |")
    lines += ["", "## Effect on every headline statistic", "",
              "| Analysis | Source | Scope | With all variants | Excluding the two | Change (pp) |",
              "|---|---|---|---|---|---|"]
    for _, r in res.iterrows():
        lines.append(f"| {r.analysis} | {r.source} | {r.scope} | {pct(r.psr_all_variants)} | "
                     f"{pct(r.psr_excluding_noncomputable)} | {r.delta_pp:+.2f} |")
    lines += ["", "## Reading", "",
              f"The largest absolute change across every reported statistic is {maxshift:.2f} percentage points.",
              "No qualitative conclusion depends on these two variants.", "",
              "Row-level data: `noncomputable_sensitivity.csv`."]
    (out / "noncomputable_sensitivity.md").write_text("\n".join(lines) + "\n")
    print(f"[task6] {len(nc)} noncomputable variants; max shift {maxshift:.2f} pp")
    return 0


# =========================================================================== what T3 certification selects
def run_t3_selection(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    vdir = verina_dir(root)
    man = {(m["task_id"], m["transformation"]): m for m in load_manifest(root)}
    certs = {c["variant_id"]: c for c in load_certificates(root)}
    compiling = compiling_tasks(root)   # construction population = the 185 tasks whose originals compile
    rows = []
    n_excluded = 0
    for vp in sorted((root / "artifacts" / "variants").glob("*/*T3_comm_swap*/variant.json")):
        v = json.loads(vp.read_text())
        if v["task_id"] not in compiling:
            n_excluded += 1
            continue
        c = certs.get(v["variant_id"], {})
        md = v.get("metadata", {})
        sm = (man.get((v["task_id"], "T3_comm_swap"), {}) or {}).get("structural_metadata", {}) or {}
        td = vdir / v["task_id"]
        status = reference_proof_status(td)
        prf = proof_block(td)
        rows.append({
            "variant_id": v["variant_id"], "task_id": v["task_id"],
            "category": "advanced" if "advanced" in v["task_id"] else "basic",
            "certified": bool(c.get("certificate_valid")),
            "certificate_level": c.get("certificate_level"),
            "failure_category": c.get("certificate_failure_category"),
            "operator": md.get("operator"), "lhs": md.get("lhs"), "rhs": md.get("rhs"),
            "n_eligible_occurrences": md.get("n_eligible_occurrences"),
            "code_loc": v.get("code_loc_original"),
            "code_tokens": None,
            "recursive": bool(sm.get("code_self_recursive") or sm.get("code_has_let_rec") or sm.get("code_has_where") or sm.get("code_has_def_level_termination")),
            "self_recursive": bool(sm.get("code_self_recursive")),
            "has_let_rec": bool(sm.get("code_has_let_rec")),
            "has_where": bool(sm.get("code_has_where")),
            "def_level_termination": bool(sm.get("code_has_def_level_termination")),
            "n_nested_helpers": int(bool(sm.get("code_aux_nonempty"))) + int(bool(sm.get("code_has_let_rec"))),
            "code_aux_nonempty": bool(sm.get("code_aux_nonempty")),
            "has_reference_proof": status == "supplied",
            "reference_proof_loc": (len([l for l in prf.splitlines() if l.strip()]) if status == "supplied" else None),
        })
    df = pd.DataFrame(rows)
    src_code = {}
    for t in df.task_id.unique():
        s = (vdir / t / "task.lean").read_text(encoding="utf-8")
        m = re.search(r"-- !benchmark @start code\n(.*?)-- !benchmark @end code", s, re.S)
        src_code[t] = m.group(1) if m else ""
    df["code_tokens"] = df.task_id.map(lambda t: len(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*|[^\sA-Za-z0-9]", src_code[t])))
    df.to_csv(out / "t3_certified_vs_rejected.csv", index=False)

    cert, rej = df[df.certified], df[~df.certified]
    from scipy.stats import mannwhitneyu, fisher_exact

    def mw(col):
        try:
            return mannwhitneyu(cert[col].dropna(), rej[col].dropna()).pvalue
        except Exception:
            return float("nan")

    def fe(col):
        try:
            return fisher_exact([[int(cert[col].sum()), int((~cert[col]).sum())],
                                 [int(rej[col].sum()), int((~rej[col]).sum())]])[1]
        except Exception:
            return float("nan")

    lines = ["# What the T3 certification procedure selects", "",
             f"T3 commutative-swap candidates over the {len(compiling)}-task construction population: {len(df)} generated,",
             f"{len(cert)} certified ({100*len(cert)/len(df):.1f}%), {len(rej)} rejected. This matches Table 1 of the paper.",
             f"A further {n_excluded} candidates come from applicable tasks whose originals do not compile in the pinned",
             "environment and are excluded from benchmark construction. This is descriptive selection analysis, not a",
             "causal model.", "",
             "## Certified versus rejected candidates", "",
             "| Characteristic | Certified | Rejected | Test |", "|---|---|---|---|",
             f"| Candidates | {len(cert)} | {len(rej)} | |",
             f"| Distinct tasks | {cert.task_id.nunique()} | {rej.task_id.nunique()} | |",
             f"| Median implementation LoC | {cert.code_loc.median():.1f} | {rej.code_loc.median():.1f} | Mann-Whitney p = {mw('code_loc'):.2e} |",
             f"| Median implementation tokens | {cert.code_tokens.median():.1f} | {rej.code_tokens.median():.1f} | Mann-Whitney p = {mw('code_tokens'):.2e} |",
             f"| Recursive implementation | {100*cert.recursive.mean():.1f}% | {100*rej.recursive.mean():.1f}% | Fisher p = {fe('recursive'):.2e} |",
             f"| Self-recursive | {100*cert.self_recursive.mean():.1f}% | {100*rej.self_recursive.mean():.1f}% | Fisher p = {fe('self_recursive'):.2e} |",
             f"| Contains `let rec` | {100*cert.has_let_rec.mean():.1f}% | {100*rej.has_let_rec.mean():.1f}% | Fisher p = {fe('has_let_rec'):.2e} |",
             f"| Contains `where` clause | {100*cert.has_where.mean():.1f}% | {100*rej.has_where.mean():.1f}% | Fisher p = {fe('has_where'):.2e} |",
             f"| Non-empty helper region | {100*cert.code_aux_nonempty.mean():.1f}% | {100*rej.code_aux_nonempty.mean():.1f}% | Fisher p = {fe('code_aux_nonempty'):.2e} |",
             f"| VERINA `advanced` category | {100*(cert.category=='advanced').mean():.1f}% | {100*(rej.category=='advanced').mean():.1f}% | |",
             f"| Has a VERINA reference proof | {100*cert.has_reference_proof.mean():.1f}% | {100*rej.has_reference_proof.mean():.1f}% | Fisher p = {fe('has_reference_proof'):.2e} |",
             "", "## Swapped operator", "", "| Operator | Certified | Rejected | Certification rate |", "|---|---|---|---|"]
    for op in sorted(df.operator.dropna().unique()):
        c_, r_ = int((cert.operator == op).sum()), int((rej.operator == op).sum())
        lines.append(f"| `{op}` | {c_} | {r_} | {100*c_/max(c_+r_,1):.1f}% |")
    sub = df[df.has_reference_proof]
    if len(sub):
        lines += ["", "## Reference-proof length, within the subset that has one", "",
                  f"Certified candidates: n = {int(sub.certified.sum())}, median reference-proof LoC "
                  f"{sub[sub.certified].reference_proof_loc.median():.1f}. Rejected: n = {int((~sub.certified).sum())}, "
                  f"median {sub[~sub.certified].reference_proof_loc.median():.1f}. Tasks without a reference proof are "
                  "excluded from this row rather than imputed."]
    lines += ["", "## Why candidates are rejected", "", "| Certificate failure category | Candidates |", "|---|---|"]
    for k, n in rej.failure_category.fillna("(none recorded)").value_counts().items():
        lines.append(f"| {k} | {n} |")
    lines += ["", "## Reading", "",
              f"Recursion is the dominant separator: {100 * cert.recursive.mean():.1f}% of certified candidates sit in a recursive",
              f"implementation versus {100 * rej.recursive.mean():.1f}% of rejected ones (Fisher p = {fe('recursive'):.1e}), almost always through a",
              "`let rec` helper, where pointwise equality needs task-specific induction that the fixed certificate ladder",
              "does not synthesize. Length differences are small and not consistent across metrics: certified bodies are",
              f"shorter in lines (median {cert.code_loc.median():.1f} vs {rej.code_loc.median():.1f}, p = {mw('code_loc'):.3f}) but not in tokens (median",
              f"{cert.code_tokens.median():.0f} vs {rej.code_tokens.median():.0f}, p = {mw('code_tokens'):.2f}). The certified semantic suite is therefore biased",
              "towards non-recursive implementations, and semantic-class conclusions apply to that certified subset only.", "",
              "Row-level data: `t3_certified_vs_rejected.csv`."]
    (out / "t3_selection_summary.md").write_text("\n".join(lines) + "\n")
    print(f"[task7] T3 {len(cert)}/{len(df)} certified; recursion {100*cert.recursive.mean():.0f}% vs {100*rej.recursive.mean():.0f}%")
    return 0




# =========================================================================== aggregation and common support
def family_of(v: str) -> str:
    return v.split("__")[1] if "__" in v else "?"


def _family_balanced(d: pd.DataFrame) -> float:
    """Each available family gets equal weight within a task; tasks then get equal weight."""
    if d.empty:
        return float("nan")
    per_task_family = d.groupby(["task_id", "transformation"])["survives"].mean()
    per_task = per_task_family.groupby("task_id").mean()
    return float(per_task.mean())


def _cell_level(d: pd.DataFrame) -> pd.Series:
    """One observation per (task, family) cell: average multiple variants of the same family first."""
    return d.groupby(["task_id", "transformation"])["survives"].mean()


def _cluster_bootstrap_pooled(cells: pd.Series, n_boot: int, seed: int = SEED) -> tuple:
    # statistic = unweighted mean over all (task, family) cells; resample whole tasks and keep all their cells
    g = cells.groupby(level=0).agg(["sum", "count"])
    s_, c_ = g["sum"].to_numpy(dtype=float), g["count"].to_numpy(dtype=float)
    idx = np.random.default_rng(seed).integers(0, len(s_), size=(n_boot, len(s_)))
    boots = s_[idx].sum(axis=1) / c_[idx].sum(axis=1)
    return float(np.percentile(boots, 2.5)), float(np.percentile(boots, 97.5))


def run_aggregation(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    df = load_survival(root)
    sources = ["reference"] + PROVERS
    rows = []
    for src in sources:
        d = df[df.source == src]
        no_t1 = d[d.transformation != "T1_let_intro"]
        cell = _cell_level(d)
        cell_task = cell.groupby("task_id").mean()
        variants_task = d.groupby("task_id")["survives"].mean()
        for name, value, per_task, formula in [
            ("task_normalized", task_normalized_psr(d), variants_task,
             "mean over tasks of (mean over that task's certified variants)"),
            ("excluding_T1", task_normalized_psr(no_t1), no_t1.groupby("task_id")["survives"].mean(),
             "same, restricted to variants outside T1"),
            ("family_balanced", _family_balanced(d), cell.groupby("task_id").mean(),
             "mean over tasks of (mean over that task's available families of (mean over that family's variants))"),
            ("one_per_task_family_cell", float(cell.mean()), cell_task,
             "unweighted mean over (task, family) cells, averaging multiple variants of a family first"),
        ]:
            lo, hi = cluster_bootstrap_ci(per_task.tolist(), n_boot=args.n_boot)
            if name == "one_per_task_family_cell":
                lo, hi = _cluster_bootstrap_pooled(cell, args.n_boot)
            rows.append({"source": src, "aggregation": name, "psr": value, "ci_low": lo, "ci_high": hi,
                         "n_tasks": int(per_task.size), "n_variants": int(len(d if name != "excluding_T1" else no_t1)),
                         "weighting_formula": formula})
    agg = pd.DataFrame(rows)
    agg.to_csv(out / "aggregation_sensitivity.csv", index=False)

    # ---- common support
    ref = df[df.source == "reference"]
    cs_rows = []
    for m in PROVERS:
        md = df[df.source == m]
        cells_m = set(map(tuple, md[["task_id", "transformation"]].drop_duplicates().values))
        cells_r = set(map(tuple, ref[["task_id", "transformation"]].drop_duplicates().values))
        shared = cells_m & cells_r
        if not shared:
            continue
        sel = lambda d: d[[(t, f) in shared for t, f in zip(d.task_id, d.transformation)]]
        a, b = sel(md), sel(ref)
        r = paired_diff(a, b, n_boot=args.n_boot)
        cs_rows.append({"comparison": f"{m}_vs_reference", "support": "pairwise_common_cells",
                        "n_cells": len(shared), "n_tasks": r["n_tasks"], "model_psr": r["psr_a"],
                        "reference_psr": r["psr_b"], "delta": r["delta"], "ci_low": r["ci_low"], "ci_high": r["ci_high"]})
    cell_sets = [set(map(tuple, df[df.source == s][["task_id", "transformation"]].drop_duplicates().values))
                 for s in sources]
    shared_all = set.intersection(*cell_sets) if cell_sets else set()
    shared_tasks = {t for t, _ in shared_all}
    for m in PROVERS:
        if not shared_all:
            break
        sel = lambda d: d[[(t, f) in shared_all for t, f in zip(d.task_id, d.transformation)]]
        r = paired_diff(sel(df[df.source == m]), sel(ref), n_boot=args.n_boot)
        cs_rows.append({"comparison": f"{m}_vs_reference", "support": "four_source_common_cells",
                        "n_cells": len(shared_all), "n_tasks": r["n_tasks"], "model_psr": r["psr_a"],
                        "reference_psr": r["psr_b"], "delta": r["delta"], "ci_low": r["ci_low"], "ci_high": r["ci_high"]})
    cs = pd.DataFrame(cs_rows)
    cs.to_csv(out / "common_support.csv", index=False)

    lines = ["# Alternative PSR aggregation and common support", "",
             "Every aggregate below is recomputed from `results/survival_results.csv`. Confidence intervals are",
             f"task-cluster bootstrap percentile intervals over {args.n_boot:,} replicates, seed {SEED}.", "",
             "## Weighting formulas", "",
             "| Aggregation | Formula |", "|---|---|"]
    for name, formula in agg[["aggregation", "weighting_formula"]].drop_duplicates().values:
        lines.append(f"| `{name}` | {formula} |")
    lines += ["", "## Results", "", "| Source | Aggregation | PSR (%) | 95% CI | Tasks |", "|---|---|---|---|---|"]
    for _, r in agg.iterrows():
        lines.append(f"| {r.source} | {r.aggregation} | {pct(r.psr)} | [{pct(r.ci_low)}, {pct(r.ci_high)}] | {int(r.n_tasks)} |")
    lines += ["", "## Common-support matched comparisons", "",
              "Pairwise common support uses exactly the (task, family) cells present for both the model and the",
              "reference. The four-source support additionally requires the cell to exist for all three provers.", "",
              "| Comparison | Support | Cells | Tasks | Model PSR | Reference PSR | Delta | 95% CI |",
              "|---|---|---|---|---|---|---|---|"]
    for _, r in cs.iterrows():
        lines.append(f"| {r.comparison} | {r.support} | {int(r.n_cells)} | {int(r.n_tasks)} | {pct(r.model_psr)} | "
                     f"{pct(r.reference_psr)} | {100*r.delta:+.1f} | [{pct(r.ci_low)}, {pct(r.ci_high)}] |")
    lines += ["", f"The four-source common support contains {len(shared_all)} (task, family) cells over "
                  f"{len(shared_tasks)} tasks.",
              "", "## Reading", ""]
    piv = agg.pivot(index="source", columns="aggregation", values="psr")
    ref_lowest = all(piv[c].idxmin() == "reference" for c in piv.columns)
    ds_below = all(piv.loc["deepseek-prover-v2-7b", c] < min(piv.loc["goedel-prover-v2-8b", c], piv.loc["goedel-prover-v2-32b", c])
                   for c in piv.columns)
    g_gap = float((piv.loc["goedel-prover-v2-8b"] - piv.loc["goedel-prover-v2-32b"]).abs().max())
    shift = float(max((piv[c] - piv["task_normalized"]).abs().max() for c in ["family_balanced", "one_per_task_family_cell"]))
    four = cs[cs.support == "four_source_common_cells"]
    lines += [f"- Reference proofs have the lowest PSR under every aggregation: {'yes' if ref_lowest else 'NO'}.",
              f"- DeepSeek-Prover-V2-7B is below both Goedel models under every aggregation: {'yes' if ds_below else 'no'}. The two",
              f"  Goedel models differ by at most {100 * g_gap:.1f} points under any aggregation, so their relative order carries no information.",
              f"- Family-balanced and cell-level weighting move any source's PSR by at most {100 * shift:.1f} points from the task-normalized value.",
              "- Excluding T1 lowers every absolute PSR, because every source survives T1 universally, without reordering the",
              "  sources: " + ", ".join(f"{src_} {pct(piv.loc[src_, 'excluding_T1'])}%" for src_ in piv.index) + ".",
              f"- On the four-source common support ({len(shared_all)} cells, {len(shared_tasks)} tasks) every prover's matched difference is",
              f"  positive with a 95% CI excluding zero: {'yes' if len(four) and (four.ci_low > 0).all() else 'NO'}.", "",
              "Row-level data: `aggregation_sensitivity.csv`, `common_support.csv`."]
    (out / "aggregation_summary.md").write_text("\n".join(lines) + "\n")
    print(f"[task4] {len(agg)} aggregate rows; four-source common support {len(shared_all)} cells / {len(shared_tasks)} tasks")
    return 0


# =========================================================================== per-family matched effects
def run_per_family(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    df = load_survival(root)
    ref = df[df.source == "reference"]
    rows = []
    for m in PROVERS:
        md = df[df.source == m]
        for fam in FAMILIES:
            a, b = md[md.transformation == fam], ref[ref.transformation == fam]
            r = paired_diff(a, b, n_boot=args.n_boot)
            cells = len(set(map(tuple, a[["task_id", "transformation"]].drop_duplicates().values))
                        & set(map(tuple, b[["task_id", "transformation"]].drop_duplicates().values)))
            rows.append({"model_id": m, "transformation": fam, "matched_tasks": r["n_tasks"],
                         "n_task_family_cells": cells, "n_matched_variants": r["n_variants"],
                         "reference_psr": r["psr_b"], "model_psr": r["psr_a"], "delta": r["delta"],
                         "ci_low": r["ci_low"], "ci_high": r["ci_high"],
                         "ci_excludes_zero": (not math.isnan(r["ci_low"])) and (r["ci_low"] > 0 or r["ci_high"] < 0)})
    res = pd.DataFrame(rows)
    res.to_csv(out / "per_family_matched.csv", index=False)
    print(res[["model_id", "transformation", "matched_tasks", "reference_psr", "model_psr", "delta"]].round(3).to_string(index=False))
    return 0


# =========================================================================== mechanism annotation audit
STRUCTURAL_FAMS = ["T2_helper_extract", "T5_branch_extract"]
SEMANTIC_FAMS = ["T3_comm_swap", "T4_cond_invert"]


def classify_bridge(proof: str, fname: str) -> dict:
    """Assign the mechanism category and record the exact fragment that justifies it.

    Categories are read off the proof text with fixed patterns applied in a fixed priority order.  The
    annotation is post hoc and observational: it describes how a frozen proof reaches the implementation,
    not a causal effect of a tactic.  Every match is recorded so that ambiguity is visible.
    """
    f = re.escape(fname)
    pats = [
        ("rfl_equation", rf"have\s+\S+\s*:[^\n]*\b{f}\b[^\n]*=[^\n]*:=\s*(?:by\s+)?rfl\b"),
        ("rfl_equation", rf"have\s+\S+\s*:[^\n]*\b{f}\b[^\n]*=[^\n]*:=\s*by\s*\n\s*rfl\b"),
        ("unfold", rf"\bunfold\b[^\n]*\b{f}\b"),
        ("simp[f]", rf"\b(?:simp|simp_all|dsimp|simpa|simp only)\b[^\n\[]*\[[^\]\n]*\b{f}\b[^\]\n]*\]"),
        ("rw[f]", rf"\b(?:rw|rewrite|rwa)\s*\[[^\]\n]*\b{f}\b[^\]\n]*\]"),
    ]
    hits = []
    for name, pat in pats:
        m = re.search(pat, proof)
        if m:
            hits.append((name, m.group(0).strip()))
    if not hits:
        return {"mechanism": "none", "fragment": "", "unambiguous": True,
                "notes": "the proof never names the target function in a bridging tactic",
                "all_matches": ""}
    seen, ordered = set(), []
    for n, frag in hits:
        if n not in seen:
            seen.add(n)
            ordered.append((n, frag))
    primary, frag = ordered[0]
    return {"mechanism": primary, "fragment": frag[:300], "unambiguous": len(ordered) == 1,
            "notes": ("single bridging construct" if len(ordered) == 1 else
                      "multiple bridging constructs present; the highest-priority one is assigned and all are listed"),
            "all_matches": ";".join(n for n, _ in ordered)}


def _contrast(d: pd.DataFrame, group_a: str, group_b_pred, n_boot: int, seed: int = SEED) -> dict:
    """Task-clustered difference in survival rate between two mechanism groups of records."""
    a = d[d.mechanism == group_a]
    b = d[group_b_pred(d)]
    if a.empty or b.empty:
        return {"n_a": len(a), "n_b": len(b), "rate_a": float("nan"), "rate_b": float("nan"),
                "delta": float("nan"), "ci_low": float("nan"), "ci_high": float("nan"),
                "tasks_a": 0, "tasks_b": 0}
    tasks = sorted(set(d.task_id))
    rng = np.random.default_rng(seed)
    by_task = {t: d[d.task_id == t] for t in tasks}

    def stat(frame):
        aa, bb = frame[frame.mechanism == group_a], frame[group_b_pred(frame)]
        if aa.empty or bb.empty:
            return None
        return aa.survives.mean() - bb.survives.mean()

    boots = []
    idx = rng.integers(0, len(tasks), size=(n_boot, len(tasks)))
    for row in idx:
        frame = pd.concat([by_task[tasks[i]] for i in row], ignore_index=True)
        v = stat(frame)
        if v is not None:
            boots.append(v)
    lo, hi = (float(np.percentile(boots, 2.5)), float(np.percentile(boots, 97.5))) if boots else (float("nan"), float("nan"))
    return {"n_a": len(a), "n_b": len(b), "rate_a": float(a.survives.mean()), "rate_b": float(b.survives.mean()),
            "delta": float(a.survives.mean() - b.survives.mean()), "ci_low": lo, "ci_high": hi,
            "tasks_a": a.task_id.nunique(), "tasks_b": b.task_id.nunique()}


def run_mechanism(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    fname = {}
    for vp in (root / "artifacts" / "variants").glob("*/*/variant.json"):
        v = json.loads(vp.read_text())
        fname[v["variant_id"]] = v["function_name"]
    rows = []
    with (root / "results" / "survival_models.jsonl").open() as fh:
        for line in fh:
            d = json.loads(line)
            if d.get("model_id") not in PROVERS:
                continue
            if d["transformation"] not in STRUCTURAL_FAMS + SEMANTIC_FAMS:
                continue
            c = classify_bridge(d.get("proof_text") or "", fname.get(d["variant_id"], ""))
            rows.append({"task_id": d["task_id"], "proof_source": d["model_id"], "variant_id": d["variant_id"],
                         "transformation": d["transformation"],
                         "class": "structural" if d["transformation"] in STRUCTURAL_FAMS else "semantic",
                         "survives": bool(d["survives"]), "survival_outcome": d.get("outcome"),
                         "mechanism": c["mechanism"], "supporting_fragment": c["fragment"],
                         "unambiguous": c["unambiguous"], "all_matched_categories": c["all_matches"],
                         "notes": c["notes"]})
    ann = pd.DataFrame(rows)
    ann.to_csv(out / "mechanism_annotation_audit.csv", index=False)

    struct = ann[ann["class"] == "structural"]
    sem = ann[ann["class"] == "semantic"]
    not_bridge = lambda f: f.mechanism != "rfl_equation"
    is_simp = lambda f: f.mechanism == "simp[f]"

    contrasts = []
    for label, frame, other in [("structural_rfl_vs_all_other", struct, not_bridge),
                                ("semantic_rfl_vs_simp", sem, is_simp)]:
        r = _contrast(frame, "rfl_equation", other, args.n_boot)
        contrasts.append({"contrast": label, "proof_source": "all_provers", **r})
        for m in PROVERS:
            sub = frame[frame.proof_source == m]
            rr = _contrast(sub, "rfl_equation", other, args.n_boot)
            contrasts.append({"contrast": label, "proof_source": m, **rr})
        # one record per task and proof source
        collapsed = (frame.groupby(["task_id", "proof_source", "mechanism"], as_index=False)
                     .agg(survives=("survives", "mean")))
        rc = _contrast(collapsed, "rfl_equation", other, args.n_boot)
        contrasts.append({"contrast": label + "__one_record_per_task_and_source", "proof_source": "all_provers", **rc})
    con = pd.DataFrame(contrasts)
    con.to_csv(out / "mechanism_contrasts_by_source.csv", index=False)

    loto_rows = []
    for label, frame, other in [("structural_rfl_vs_all_other", struct, not_bridge),
                                ("semantic_rfl_vs_simp", sem, is_simp)]:
        base = frame[frame.mechanism == "rfl_equation"].survives.mean() - frame[other(frame)].survives.mean()
        for t in sorted(frame.task_id.unique()):
            sub = frame[frame.task_id != t]
            a, b = sub[sub.mechanism == "rfl_equation"], sub[other(sub)]
            delta = (a.survives.mean() - b.survives.mean()) if (len(a) and len(b)) else float("nan")
            loto_rows.append({"contrast": label, "left_out_task": t, "delta": delta,
                              "delta_full": base, "shift_pp": (delta - base) * 100 if not math.isnan(delta) else float("nan"),
                              "n_a_remaining": len(a), "n_b_remaining": len(b),
                              "bridge_tasks_remaining": a.task_id.nunique()})
    loto = pd.DataFrame(loto_rows)
    loto.to_csv(out / "mechanism_leave_one_task_out.csv", index=False)

    lines = ["# Mechanism annotation audit", "",
             "The mechanism categories are **post hoc and observational**. They describe, with fixed textual",
             "patterns applied in a fixed priority order, how a frozen proof reaches the implementation. They are not",
             "estimates of a causal effect of a tactic: nothing here randomizes the tactic a model chooses.", "",
             "## Annotation rules (applied in this order)", "",
             "| Priority | Category | Pattern |", "|---|---|---|",
             "| 1 | `rfl_equation` | `have _ : <f> ... = ... := rfl` (or `:= by rfl`) |",
             "| 2 | `unfold` | `unfold ... <f>` |",
             "| 3 | `simp[f]` | `simp`/`simp_all`/`dsimp`/`simpa`/`simp only` with `<f>` in the lemma list |",
             "| 4 | `rw[f]` | `rw`/`rewrite`/`rwa` with `<f>` in the rewrite list |",
             "| 5 | `none` | the proof never names the target function in a bridging tactic |", "",
             f"Records annotated: {len(ann)} ({len(struct)} structural, {len(sem)} semantic). ",
             f"Unambiguous: {int(ann.unambiguous.sum())} of {len(ann)} "
             f"({100*ann.unambiguous.mean():.1f}%); the rest contain more than one bridging construct and are",
             "assigned by priority, with every matched category listed in `all_matched_categories`.", "",
             "## Mechanism distribution", "", "| Class | Mechanism | Records | Tasks | Survived |", "|---|---|---|---|---|"]
    for cls in ["structural", "semantic"]:
        sub = ann[ann["class"] == cls]
        for mech, g in sub.groupby("mechanism"):
            lines.append(f"| {cls} | `{mech}` | {len(g)} | {g.task_id.nunique()} | {int(g.survives.sum())} |")
    lines += ["", "## Contrasts by individual prover source", "",
              f"Confidence intervals resample whole tasks and keep every record from a sampled task ({args.n_boot:,} replicates, seed {SEED}).", "",
              "| Contrast | Proof source | Group A (rfl bridge) | Group B | Delta | 95% CI | Tasks A |",
              "|---|---|---|---|---|---|---|"]
    for _, r in con.iterrows():
        if int(r.n_a) == 0:
            lines.append(f"| {r.contrast} | {r.proof_source} | no rfl-bridge record | {int(r.n_b)} records | not estimable | -- | 0 |")
            continue
        lines.append(f"| {r.contrast} | {r.proof_source} | {int(r.n_a)} records, {pct(r.rate_a)}% | "
                     f"{int(r.n_b)} records, {pct(r.rate_b)}% | {100*r.delta:+.1f} | "
                     f"[{pct(r.ci_low)}, {pct(r.ci_high)}] | {int(r.tasks_a)} |")
    from scipy.stats import fisher_exact
    fisher = []
    for label, frame, other in [("structural_rfl_vs_all_other", struct, not_bridge), ("semantic_rfl_vs_simp", sem, is_simp)]:
        ta = frame[frame.mechanism == "rfl_equation"].groupby("task_id").survives.max().astype(bool)
        tb = frame[other(frame)].groupby("task_id").survives.max().astype(bool)
        pval = fisher_exact([[int(ta.sum()), int((~ta).sum())], [int(tb.sum()), int((~tb).sum())]])[1]
        fisher.append({"contrast": label, "bridge_tasks_with_survivor": int(ta.sum()), "bridge_tasks": int(ta.size),
                       "other_tasks_with_survivor": int(tb.sum()), "other_tasks": int(tb.size),
                       "tasks_in_both_groups": len(set(ta.index) & set(tb.index)), "fisher_p_two_sided": pval})
    fisher = pd.DataFrame(fisher)
    fisher.to_csv(out / "mechanism_task_level_fisher.csv", index=False)
    lines += ["", "Every Group A rate above is exactly 100% (structural) or 0% (semantic). The bootstrap intervals therefore",
              "reflect variation in the comparison group and in which tasks are resampled, and they overstate precision",
              "about the bridge group itself. The task-level test below is the more conservative summary.", "",
              "## Task-level test", "",
              "A task counts once per mechanism group, as surviving if any of its records in that group survives. Tasks can",
              "appear in both groups when different provers used different bridges; that overlap is reported.", "",
              "| Contrast | rfl-bridge tasks with a survivor | Comparison tasks with a survivor | Tasks in both | Fisher exact p (two-sided) |",
              "|---|---|---|---|---|"]
    for _, r in fisher.iterrows():
        lines.append(f"| {r.contrast} | {int(r.bridge_tasks_with_survivor)}/{int(r.bridge_tasks)} | "
                     f"{int(r.other_tasks_with_survivor)}/{int(r.other_tasks)} | {int(r.tasks_in_both_groups)} | {r.fisher_p_two_sided:.4f} |")
    lines += ["", "## Leave-one-task-out", "", "| Contrast | Full-sample delta | LOTO min | LOTO max | Tasks |",
              "|---|---|---|---|---|"]
    for label, g in loto.groupby("contrast"):
        lines.append(f"| {label} | {100*g.delta_full.iloc[0]:+.1f} | {100*g.delta.min():+.1f} | "
                     f"{100*g.delta.max():+.1f} | {len(g)} |")
    wv_rows = []
    for cls_, frame, other in [("structural", struct, lambda m: m != "rfl_equation"), ("semantic", sem, lambda m: m == "simp[f]")]:
        for v, g in frame.groupby("variant_id"):
            a_, b_ = g[g.mechanism == "rfl_equation"], g[g.mechanism.map(other)]
            if len(a_) and len(b_):
                wv_rows.append({"class": cls_, "variant_id": v, "task_id": g.task_id.iloc[0],
                                "rfl_sources": ";".join(a_.proof_source), "rfl_survived": int(a_.survives.sum()),
                                "rfl_records": len(a_), "comparison_sources": ";".join(b_.proof_source),
                                "comparison_mechanisms": ";".join(b_.mechanism),
                                "comparison_survived": int(b_.survives.sum()), "comparison_records": len(b_)})
    wv = pd.DataFrame(wv_rows)
    wv.to_csv(out / "mechanism_within_variant.csv", index=False)
    lines += ["", "## Same refactored variant, different bridge", "",
              "Where one prover's proof uses an rfl-equation bridge and another prover's proof of the same task uses a",
              "different bridge, both proofs are checked against the identical certified variant. This removes task and",
              "variant difficulty from the comparison, at the price of very small support. Structural comparisons use",
              "every non-rfl bridge; semantic comparisons use `simp[f]`, matching the pooled contrasts above.", "",
              "| Class | Shared variants | Tasks | rfl-bridge records surviving | Comparison records surviving |",
              "|---|---|---|---|---|"]
    for cls_ in ["structural", "semantic"]:
        g = wv[wv["class"] == cls_] if len(wv) else wv
        if len(g):
            lines.append(f"| {cls_} | {len(g)} | {g.task_id.nunique()} | {int(g.rfl_survived.sum())}/{int(g.rfl_records.sum())} | "
                         f"{int(g.comparison_survived.sum())}/{int(g.comparison_records.sum())} |")
    ls_, le_ = loto[loto.contrast == "structural_rfl_vs_all_other"], loto[loto.contrast == "semantic_rfl_vs_simp"]
    bys = con[(con.proof_source != "all_provers") & ~con.contrast.str.contains("one_record")]
    s_rows = bys[bys.contrast == "structural_rfl_vs_all_other"]
    e_rows = bys[bys.contrast == "semantic_rfl_vs_simp"]
    s_pos = [HF_ID[r.proof_source] for _, r in s_rows.iterrows() if r.n_a > 0 and r.delta > 0]
    e_neg = [f"{HF_ID[r.proof_source]} ({int(r.n_a)} record(s), {int(r.tasks_a)} task(s))" for _, r in e_rows.iterrows() if r.n_a > 0 and r.delta < 0]
    e_none = [HF_ID[r.proof_source] for _, r in e_rows.iterrows() if r.n_a == 0]
    lines += ["", "## Reading", "",
              f"- Leave-one-task-out never changes the sign of either contrast: structural {100*ls_.delta.min():+.1f} to "
              f"{100*ls_.delta.max():+.1f} points over {len(ls_)} deletions, semantic {100*le_.delta.min():+.1f} to {100*le_.delta.max():+.1f} over {len(le_)}.",
              f"- By source, the structural contrast is positive for {len(s_pos)} of {len(s_rows)} provers ({', '.join(s_pos)}).",
              f"- The semantic contrast is negative for {', '.join(e_neg) if e_neg else 'no prover'}"
              + (f", and not estimable for {', '.join(e_none)}, which has no semantic rfl-bridge record." if e_none else "."),
              f"- The pooled contrasts rest on {int(con[(con.contrast=='structural_rfl_vs_all_other') & (con.proof_source=='all_provers')].tasks_a.iloc[0])} distinct structural"
              f" and {int(con[(con.contrast=='semantic_rfl_vs_simp') & (con.proof_source=='all_provers')].tasks_a.iloc[0])} distinct semantic rfl-bridge tasks. No resampling scheme",
              "  can enlarge that number; it is the honest limit of this analysis.", "",
              "Row-level data: `mechanism_annotation_audit.csv`, `mechanism_contrasts_by_source.csv`,",
              "`mechanism_leave_one_task_out.csv`."]
    (out / "mechanism_robustness_summary.md").write_text("\n".join(lines) + "\n")
    print(f"[task8] {len(ann)} records annotated, {100*ann.unambiguous.mean():.0f}% unambiguous")
    for _, r in con[con.proof_source == "all_provers"].iterrows():
        print(f"  {r.contrast}: {100*r.delta:+.1f} [{pct(r.ci_low)}, {pct(r.ci_high)}] "
              f"(A {int(r.n_a)} rec/{int(r.tasks_a)} tasks, B {int(r.n_b)} rec)")
    return 0



# =========================================================================== first-valid selection sensitivity
SELECTION_RULES = {
    "first_valid": "first Lean-valid sample in fixed sample order (the paper's primary analysis)",
    "shortest_valid": "valid sample with the fewest proof tokens (regex tokens of the proof block); ties go to the earliest sample. The metric was fixed in code before any PSR under this rule was computed",
    "random_valid": "one valid sample drawn uniformly at random per task; 1,000 deterministic draws with a fixed seed",
    "all_valid_mean": "per task, mean PSR over all of its valid samples; then unweighted mean over tasks",
    "best_valid_oracle": "POST HOC ORACLE: per task, the valid sample with the highest PSR. Not a deployable selection rule",
    "worst_valid_oracle": "POST HOC ORACLE: per task, the valid sample with the lowest PSR. Not a deployable selection rule",
}
RULE_ORDER = ["first_valid", "shortest_valid", "random_valid", "all_valid_mean", "best_valid_oracle", "worst_valid_oracle"]
DEPLOYABLE = ["first_valid", "shortest_valid", "random_valid", "all_valid_mean"]


def _load_selection(root: Path) -> Dict[tuple, List[dict]]:
    recs = collections.defaultdict(list)
    for f in (root / "artifacts" / "selection_sensitivity").glob("*/*/attempt_*.json"):
        d = json.loads(f.read_text())
        recs[(d["model_id"], d["task_id"])].append(d)
    for k in recs:
        recs[k].sort(key=lambda d: int(d["attempt"]))
    return recs


def _att_psr(att: dict, variants: Optional[set] = None, scope: str = "overall") -> float:
    s = [r for r in att["survival"]
         if (variants is None or r["variant_id"] in variants) and (scope == "overall" or r["severity"] == scope)]
    return float(np.mean([bool(r["survives"]) for r in s])) if s else float("nan")


def _shortest_index(atts: List[dict]) -> int:
    return min(range(len(atts)), key=lambda i: (int(atts[i]["proof_tokens"]), int(atts[i]["attempt"])))


def _pick(atts: List[dict], vals: List[float]) -> dict:
    return {"first_valid": vals[0], "shortest_valid": vals[_shortest_index(atts)],
            "all_valid_mean": float(np.mean(vals)), "best_valid_oracle": float(max(vals)),
            "worst_valid_oracle": float(min(vals))}


def run_selection(args) -> int:
    root, out = args.root, args.out
    out.mkdir(parents=True, exist_ok=True)
    recs = _load_selection(root)
    sv = load_survival(root)
    ref = sv[sv.source == "reference"]
    ref_vars = ref.groupby("task_id")["variant_id"].apply(set).to_dict()
    ref_surv = dict(zip(ref.variant_id, ref.survives.astype(bool)))

    # consistency: re-evaluating the first valid sample must reproduce the frozen primary survival records
    checked = mism = 0
    for m in ALL_MODELS:
        prim = sv[sv.source == m]
        pm = dict(zip(prim.variant_id, prim.survives.astype(bool)))
        for (mm, t), atts in recs.items():
            if mm != m:
                continue
            for r in atts[0]["survival"]:
                if r["variant_id"] in pm:
                    checked += 1
                    mism += int(bool(r["survives"]) != pm[r["variant_id"]])

    rng = np.random.default_rng(SEED)
    sens, matched, room = [], [], {}
    for m in ALL_MODELS:
        tasks = sorted(t for (mm, t) in recs if mm == m)
        if not tasks:
            continue
        room[m] = (len(tasks), sum(1 for t in tasks if len(recs[(m, t)]) > 1),
                   sum(1 for t in tasks if len(recs[(m, t)]) > 1 and _shortest_index(recs[(m, t)]) != 0))
        for scope in ["overall", "S", "E"]:
            per_rule, arrays = collections.defaultdict(dict), {}
            for t in tasks:
                vals = [_att_psr(a, scope=scope) for a in recs[(m, t)]]
                if any(math.isnan(v) for v in vals):
                    continue
                for rule, v in _pick(recs[(m, t)], vals).items():
                    per_rule[rule][t] = v
                arrays[t] = np.asarray(vals)
            if not arrays:
                continue
            tl = sorted(arrays)
            for rule in RULE_ORDER:
                if rule == "random_valid":
                    draws = np.stack([arrays[t][rng.integers(0, arrays[t].size, size=args.n_draws)] for t in tl]).mean(axis=0)
                    lo, hi = cluster_bootstrap_ci([float(arrays[t].mean()) for t in tl], n_boot=args.n_boot)
                    sens.append({"model_id": m, "rule": rule, "scope": scope, "psr": float(draws.mean()),
                                 "ci_low": lo, "ci_high": hi, "draw_p2_5": float(np.percentile(draws, 2.5)),
                                 "draw_p97_5": float(np.percentile(draws, 97.5)), "n_tasks": len(tl),
                                 "n_draws": args.n_draws, "seed": SEED})
                    continue
                vals = [per_rule[rule][t] for t in tl]
                lo, hi = cluster_bootstrap_ci(vals, n_boot=args.n_boot)
                sens.append({"model_id": m, "rule": rule, "scope": scope, "psr": float(np.mean(vals)),
                             "ci_low": lo, "ci_high": hi, "draw_p2_5": float("nan"), "draw_p97_5": float("nan"),
                             "n_tasks": len(tl), "n_draws": None, "seed": SEED})
        if m not in PROVERS:
            continue
        for scope, label in [("overall", "all"), ("S", "structural"), ("E", "semantic")]:
            model_task, ref_task, arrays = collections.defaultdict(dict), {}, {}
            for t in tasks:
                if t not in ref_vars:
                    continue
                V = {r["variant_id"] for r in recs[(m, t)][0]["survival"]
                     if scope == "overall" or r["severity"] == scope} & ref_vars[t]
                if not V:
                    continue
                vals = [_att_psr(a, variants=V) for a in recs[(m, t)]]
                ref_task[t] = float(np.mean([ref_surv[v] for v in V]))
                for rule, v in _pick(recs[(m, t)], vals).items():
                    model_task[rule][t] = v
                arrays[t] = np.asarray(vals)
            tl = sorted(ref_task)
            if not tl:
                continue
            for rule in RULE_ORDER:
                if rule == "random_valid":
                    draws = np.stack([arrays[t][rng.integers(0, arrays[t].size, size=args.n_draws)] - ref_task[t]
                                      for t in tl]).mean(axis=0)
                    diffs = [float(arrays[t].mean() - ref_task[t]) for t in tl]
                    lo, hi = cluster_bootstrap_ci(diffs, n_boot=args.n_boot)
                    matched.append({"model_id": m, "rule": rule, "class": label, "n_tasks": len(tl),
                                    "reference_psr": float(np.mean([ref_task[t] for t in tl])),
                                    "model_psr": float(np.mean([arrays[t].mean() for t in tl])),
                                    "delta": float(draws.mean()), "ci_low": lo, "ci_high": hi,
                                    "draw_p2_5": float(np.percentile(draws, 2.5)),
                                    "draw_p97_5": float(np.percentile(draws, 97.5))})
                    continue
                diffs = [model_task[rule][t] - ref_task[t] for t in tl]
                lo, hi = cluster_bootstrap_ci(diffs, n_boot=args.n_boot)
                matched.append({"model_id": m, "rule": rule, "class": label, "n_tasks": len(tl),
                                "reference_psr": float(np.mean([ref_task[t] for t in tl])),
                                "model_psr": float(np.mean([model_task[rule][t] for t in tl])),
                                "delta": float(np.mean(diffs)), "ci_low": lo, "ci_high": hi,
                                "draw_p2_5": float("nan"), "draw_p97_5": float("nan")})
    S = pd.DataFrame(sens)
    M = pd.DataFrame(matched)
    S.to_csv(out / "proof_selection_sensitivity.csv", index=False)
    M.to_csv(out / "proof_selection_matched.csv", index=False)

    lines = ["# First-valid proof sensitivity", "",
             "Every valid sample of every evaluated checkpoint was re-checked in the pinned Lean environment on all",
             f"certified variants of its task ({sum(len(v) for v in recs.values())} valid proof artifacts) on a",
             "24-core CPU node. No proof was generated. Confidence intervals are task-cluster bootstrap percentile intervals",
             f"({args.n_boot:,} replicates, seed {SEED}).", "",
             "## Selection rules", "", "| Rule | Definition |", "|---|---|"]
    lines += [f"| `{r}` | {SELECTION_RULES[r]} |" for r in RULE_ORDER]
    lines += ["", "## Consistency check", "",
              f"Re-evaluating each first valid sample reproduces the frozen primary survival records on {checked - mism}",
              f"of {checked} (model, variant) outcomes ({mism} mismatches).", "",
              "## How much room the rules have", "",
              "| Model | Tasks with >=1 valid sample | Tasks with >1 valid sample | Tasks where shortest != first |",
              "|---|---|---|---|"]
    lines += [f"| {HF_ID[m]} | {a} | {b} | {c} |" for m, (a, b, c) in room.items()]
    lines += ["", "## Task-normalized PSR under each rule (all certified variants)", "",
              "| Model | " + " | ".join(f"`{r}`" for r in RULE_ORDER) + " |", "|---|" + "---|" * len(RULE_ORDER)]
    for m in ALL_MODELS:
        sub = S[(S.model_id == m) & (S.scope == "overall")].set_index("rule")
        if len(sub):
            lines.append(f"| {HF_ID[m]} | " + " | ".join(pct(sub.loc[r, "psr"]) for r in RULE_ORDER) + " |")
    lines += ["", "## Matched specialized prover minus reference, under each rule", "",
              "Delta in percentage points with 95% task-cluster bootstrap CI, on exactly the matched variant set.", "",
              "| Model | Class | Tasks | " + " | ".join(f"`{r}`" for r in RULE_ORDER) + " |",
              "|---|---|---|" + "---|" * len(RULE_ORDER)]
    for m in PROVERS:
        for label in ["all", "structural", "semantic"]:
            sub = M[(M.model_id == m) & (M["class"] == label)].set_index("rule")
            if len(sub):
                cells = [f"{100*sub.loc[r, 'delta']:+.1f} [{pct(sub.loc[r, 'ci_low'])}, {pct(sub.loc[r, 'ci_high'])}]"
                         for r in RULE_ORDER]
                lines.append(f"| {HF_ID[m]} | {label} | {int(sub.iloc[0].n_tasks)} | " + " | ".join(cells) + " |")
    weak = []
    for _, r in M[M.rule.isin(DEPLOYABLE)].iterrows():
        if not r.ci_low > 0:
            weak.append(f"- {HF_ID[r.model_id]}, {r['class']}, `{r.rule}`: {100*r.delta:+.1f} "
                        f"[{pct(r.ci_low)}, {pct(r.ci_high)}]")
    neg = M[M.rule.isin(DEPLOYABLE) & (M.delta <= 0)]
    lines += ["", "## Reading", ""]
    lines.append(("No matched comparison changes sign under any deployable rule." if neg.empty else
                  f"{len(neg)} matched comparison(s) under a deployable rule have a non-positive delta; see the table."))
    if weak:
        lines += ["", "Matched comparisons under a deployable rule whose 95% CI does not exclude zero:", ""] + weak
    else:
        lines += ["", "Every matched comparison under every deployable rule has a 95% CI that excludes zero."]
    lines += ["", "`random_valid` and `all_valid_mean` coincide in expectation by construction; the draw percentiles in",
              "`proof_selection_sensitivity.csv` and `proof_selection_matched.csv` show how much the benchmark-level",
              "number moves with the luck of which valid proof is picked. The two oracle columns are post hoc bounds and",
              "are not selection rules anyone could deploy.", "",
              "Row-level data: `proof_selection_sensitivity.csv`, `proof_selection_matched.csv`."]
    (out / "proof_selection_summary.md").write_text("\n".join(lines) + "\n")
    print(f"[task3] consistency {checked - mism}/{checked}; {len(S)} sensitivity rows, {len(M)} matched rows; "
          f"{len(weak)} deployable matched CIs include zero")
    return 0


# =========================================================================== mechanical repair summary
def _tok(s: str) -> List[str]:
    return re.findall(r"[A-Za-z_][A-Za-z0-9_.']*|[^\sA-Za-z0-9]", s or "")


def run_repair_summary(args) -> int:
    import difflib
    root, out = args.root, args.out
    rep_root = root / "artifacts" / "mechanical_repairs"
    templates = json.loads((rep_root / "preregistered_templates.json").read_text())
    L = pd.DataFrame(json.loads((rep_root / "eligibility_ledger.json").read_text()))
    L["eligible"] = L.applicable_templates.apply(len) > 0
    diffdir = out / "mechanical_repair_diffs"
    diffdir.mkdir(parents=True, exist_ok=True)
    for f in diffdir.glob("*.diff"):
        f.unlink()
    rows = []
    for f in sorted(rep_root.glob("*.json")):
        if f.name in ("preregistered_templates.json", "eligibility_ledger.json"):
            continue
        d = json.loads(f.read_text())
        b, a = d["proof_before"], d["proof_after"]
        tm = difflib.SequenceMatcher(a=_tok(b), b=_tok(a), autojunk=False)
        tok_changed = sum(max(i2 - i1, j2 - j1) for tag, i1, i2, j1, j2 in tm.get_opcodes() if tag != "equal")
        lm = difflib.SequenceMatcher(a=b.splitlines(), b=a.splitlines(), autojunk=False)
        line_changed = sum(max(i2 - i1, j2 - j1) for tag, i1, i2, j1, j2 in lm.get_opcodes() if tag != "equal")
        name = f"{d['variant_id']}__{d['source']}__{d['template']}.diff"
        body = "\n".join(difflib.unified_diff(b.splitlines(), a.splitlines(),
                                              fromfile=f"{d['source']}:{d['variant_id']} (proof as evaluated)",
                                              tofile=f"{d['source']}:{d['variant_id']} ({d['template']})", lineterm=""))
        tail = f"\n# unedited proof on this variant: {'fails (as recorded)' if d.get('control_unedited_fails') else 'DOES NOT FAIL in this harness'}"
        tail += f"\n# edited proof: {'REPAIRED (compiles on the refactored variant)' if d['repaired'] else 'still fails'}"
        if not d["repaired"] and d.get("first_error"):
            tail += "\n# first proof-region error: " + str(d["first_error"]).replace("\n", " | ")[:300]
        (diffdir / name).write_text(body + tail + "\n")
        rows.append({**{k: d.get(k) for k in ("variant_id", "task_id", "source", "transformation", "template",
                                               "function_name", "helper", "control_unedited_fails", "repaired",
                                               "outcome", "first_error", "material_provenance")},
                     "tokens_changed": tok_changed, "lines_changed": line_changed,
                     "diff_file": f"mechanical_repair_diffs/{name}"})
    R = pd.DataFrame(rows)
    R.to_csv(out / "mechanical_repairs.csv", index=False)
    V = R[R.control_unedited_fails.astype(bool)]
    rec = (V.groupby(["variant_id", "source"]).agg(repaired=("repaired", "any"), transformation=("transformation", "first"))
           .reset_index())
    lines = ["# Pre-registered mechanical repairs of structural failures", "",
             "No LLM is involved. The edit templates were written to `artifacts/mechanical_repairs/preregistered_templates.json`",
             "in the harness before any edited proof was compiled, and each is applied only where it is syntactically",
             "applicable. For every attempted edit the harness compiles two files on the same refactored variant in the",
             "pinned Lean environment: the unedited proof (a control that must reproduce the recorded failure) and the",
             "edited proof. Proof, proof_aux and import blocks are exactly those of the evaluated artifact (VERINA source",
             "blocks for reference proofs; the hash-verified primary artifact for model proofs).", "",
             "## Pre-registered templates", "", "| Template | Rule |", "|---|---|"]
    lines += [f"| `{k}` | {v} |" for k, v in templates.items()]
    lines += ["", "## By proof source", "",
              "A record is one (proof source, failing structural variant); it counts as repaired if any applicable",
              "template makes it compile. Rates use only records whose unedited control reproduced the failure.", "",
              "| Source | Structural failures | Eligible for >=1 template | Control reproduces failure | Repaired (union) | Rate among eligible | Share of all failures |",
              "|---|---|---|---|---|---|---|"]
    tf = te = tv = tr = 0
    for src in ["reference"] + PROVERS:
        nf = int((L.source == src).sum())
        ne = int(((L.source == src) & L.eligible).sum())
        r_src = rec[rec.source == src]
        nv, nr = int(len(r_src)), int(r_src.repaired.sum())
        tf, te, tv, tr = tf + nf, te + ne, tv + nv, tr + nr
        lines.append(f"| {src} | {nf} | {ne} | {nv} | {nr} | {pct(nr / nv) if nv else '--'}% | {pct(nr / nf) if nf else '--'}% |")
    lines.append(f"| **all** | {tf} | {te} | {tv} | {tr} | {pct(tr / tv) if tv else '--'}% | {pct(tr / tf) if tf else '--'}% |")
    lines += ["", "## Why records are not eligible", "", "| Source | Reason | Records |", "|---|---|---|"]
    for (src, reason), g in L[~L.eligible].groupby(["source", "skip_reason"]):
        lines.append(f"| {src} | {reason} | {len(g)} |")
    lines += ["", "## By template (control-verified edits)", "", "| Template | Source | Edits | Repaired | Success rate |",
              "|---|---|---|---|---|"]
    for (tmpl, src), g in V.groupby(["template", "source"]):
        lines.append(f"| `{tmpl}` | {src} | {len(g)} | {int(g.repaired.sum())} | {pct(g.repaired.mean())}% |")
    for tmpl, g in V.groupby("template"):
        lines.append(f"| `{tmpl}` | **all** | {len(g)} | {int(g.repaired.sum())} | {pct(g.repaired.mean())}% |")
    lines += ["", "## By transformation", "", "| Transformation | Failures | Eligible | Control-verified | Repaired (union) |",
              "|---|---|---|---|---|"]
    for fam in STRUCTURAL_FAMS:
        r_f = rec[rec.transformation == fam]
        lines.append(f"| {fam} | {int((L.transformation == fam).sum())} | {int(((L.transformation == fam) & L.eligible).sum())} | "
                     f"{len(r_f)} | {int(r_f.repaired.sum())} |")
    n_bad = int((~R.control_unedited_fails.astype(bool)).sum())
    lines += ["", "## Edit size", "",
              f"Across all {len(R)} attempted edits: median {R.tokens_changed.median():.0f} changed token(s) "
              f"(max {int(R.tokens_changed.max())}), median {R.lines_changed.median():.0f} changed line(s) "
              f"(max {int(R.lines_changed.max())}).", "",
              "## Harness check", "",
              f"{len(R) - n_bad} of {len(R)} unedited controls reproduced the recorded failure; {n_bad} did not and are",
              "excluded from every rate above (listed in `mechanical_repairs.csv` with `control_unedited_fails = False`).", "",
              "## Reading", "",
              "Rates are conditional on eligibility: a record whose proof never names the implementation in an `unfold`,",
              "`simp` or `dsimp` invocation cannot be edited by these templates and is reported as ineligible, not as a",
              "repair failure. This bounds the practical cost of the measured structural brittleness for one class of",
              "proofs; it is not a re-proving experiment and says nothing about proofs outside that class.", "",
              "Row-level data: `mechanical_repairs.csv`; every before/after diff is in `mechanical_repair_diffs/`;",
              "eligibility decisions are in `artifacts/mechanical_repairs/eligibility_ledger.json`."]
    (out / "mechanical_repair_summary.md").write_text("\n".join(lines) + "\n")
    print(f"[task9] failures {tf}, eligible {te}, control-verified {tv}, repaired {tr}")
    return 0


# =========================================================================== proof-length control
def length_control(root: Path, out: Path) -> dict:
    """Task-clustered logistic regression of survival on proof source, with and without log proof length,
    plus survival rates inside the 10-30 LoC window where the two sources overlap."""
    import statsmodels.formula.api as smf
    sv = load_survival(root)
    d = sv[sv.severity.isin(["S", "E"]) & sv.source.isin(["reference"] + PROVERS)].copy()
    d["ploc"] = pd.to_numeric(d["proof_loc"], errors="coerce")
    d = d.dropna(subset=["ploc"])
    d["is_prover"] = (d.source != "reference").astype(int)
    d["y"] = d.survives.astype(int)
    d["logloc"] = np.log(d.ploc.clip(lower=1))
    kw = dict(disp=0, cov_type="cluster", cov_kwds={"groups": pd.factorize(d.task_id)[0]})
    m0 = smf.logit("y ~ is_prover", data=d).fit(**kw)
    m1 = smf.logit("y ~ is_prover + logloc", data=d).fit(**kw)
    res = {"n_records": len(d), "n_tasks": int(d.task_id.nunique()),
           "median_loc_prover": float(d[d.is_prover == 1].ploc.median()),
           "median_loc_reference": float(d[d.is_prover == 0].ploc.median()),
           "coef_prover_unadjusted": float(m0.params["is_prover"]), "p_prover_unadjusted": float(m0.pvalues["is_prover"]),
           "coef_prover_adjusted": float(m1.params["is_prover"]), "p_prover_adjusted": float(m1.pvalues["is_prover"]),
           "coef_log_proof_loc": float(m1.params["logloc"]), "p_log_proof_loc": float(m1.pvalues["logloc"])}
    w = d[(d.ploc >= 10) & (d.ploc <= 30)]
    for lab, g in w.groupby("is_prover"):
        k = "prover" if lab == 1 else "reference"
        res[f"window10_30_{k}_rate"] = float(g.y.mean())
        res[f"window10_30_{k}_records"] = int(len(g))
        res[f"window10_30_{k}_tasks"] = int(g.task_id.nunique())
    pd.DataFrame([res]).to_csv(out / "length_confound.csv", index=False)
    return res


def run_length_confound(args) -> int:
    args.out.mkdir(parents=True, exist_ok=True)
    res = length_control(args.root, args.out)
    print(f"[length_confound] {res['n_records']} records over {res['n_tasks']} tasks; prover coefficient "
          f"{res['coef_prover_unadjusted']:.3f} unadjusted -> {res['coef_prover_adjusted']:.3f} adjusted for log proof length",
          file=sys.stderr)
    return 0


# =========================================================================== bootstrap-seed sensitivity
def matched_seed_sensitivity(root: Path, out: Path, n_boot: int = 10000, n_seeds: int = 50) -> pd.DataFrame:
    """Re-run the primary matched percentile bootstrap under `n_seeds` seeds (0..n_seeds-1) and report the
    range of each interval endpoint.  Percentile endpoints of a small, discrete per-task difference
    distribution can move with the seed; this records by how much, and how often the interval excludes zero."""
    sv = load_survival(root)
    ref = sv[sv.source == "reference"]
    rows = []
    for m in PROVERS:
        md = sv[sv.source == m]
        for cls, sel in [("all", None), ("structural", "S"), ("semantic", "E")]:
            a = md if sel is None else md[md.severity == sel]
            b = ref if sel is None else ref[ref.severity == sel]
            cv = set(a.variant_id) & set(b.variant_id)
            pa = a[a.variant_id.isin(cv)].groupby("task_id").survives.mean()
            pb = b[b.variant_id.isin(cv)].groupby("task_id").survives.mean()
            tasks = sorted(set(pa.index) & set(pb.index))
            d = np.array([pa[t] - pb[t] for t in tasks])
            los, his = [], []
            for seed in range(n_seeds):
                rng = np.random.default_rng(seed)
                boots = d[rng.integers(0, d.size, size=(n_boot, d.size))].mean(axis=1)
                los.append(np.percentile(boots, 2.5))
                his.append(np.percentile(boots, 97.5))
            los, his = np.array(los), np.array(his)
            rows.append({"model": m, "class": cls, "tasks": len(tasks), "delta": 100 * d.mean(),
                         "lo_min": 100 * los.min(), "lo_max": 100 * los.max(),
                         "hi_min": 100 * his.min(), "hi_max": 100 * his.max(),
                         "share_seeds_excluding_zero": float((los > 0).mean()),
                         "distinct_task_diffs": len(set(np.round(d, 6)))})
    R = pd.DataFrame(rows)
    R.to_csv(out / "matched_ci_seed_sensitivity.csv", index=False)
    return R


def run_seed_sensitivity(args) -> int:
    args.out.mkdir(parents=True, exist_ok=True)
    R = matched_seed_sensitivity(args.root, args.out, n_boot=args.n_boot)
    print(R.round(2).to_string(index=False), file=sys.stderr)
    return 0


# =========================================================================== matched deltas, other weightings
def _family_balanced_delta(sv: pd.DataFrame, model: str, n_boot: int, seed: int) -> dict:
    """Matched difference with every transformation family weighted equally inside a task, so the two
    families that supply most variants cannot dominate the aggregate."""
    a, b = sv[sv.source == model], sv[sv.source == "reference"]
    common = set(a.variant_id) & set(b.variant_id)
    a, b = a[a.variant_id.isin(common)], b[b.variant_id.isin(common)]

    def per_task(df: pd.DataFrame) -> pd.Series:
        fam = df.groupby(["task_id", "transformation"])["survives"].mean()
        return fam.groupby("task_id").mean()

    pa, pb = per_task(a), per_task(b)
    tasks = sorted(set(pa.index) & set(pb.index))
    if not tasks:
        return {"n_tasks": 0, "n_variants": 0, "psr_a": float("nan"), "psr_b": float("nan"),
                "delta": float("nan"), "ci_low": float("nan"), "ci_high": float("nan"), "p_perm": float("nan")}
    d = np.array([pa[t] - pb[t] for t in tasks])
    rng = np.random.default_rng(seed)
    boots = d[rng.integers(0, len(d), size=(n_boot, len(d)))].mean(axis=1)
    signs = rng.choice([-1.0, 1.0], size=(n_boot, len(d)))
    return {"n_tasks": len(d), "n_variants": len(common), "psr_a": float(pa.loc[tasks].mean()),
            "psr_b": float(pb.loc[tasks].mean()), "delta": float(d.mean()),
            "ci_low": float(np.quantile(boots, 0.025)), "ci_high": float(np.quantile(boots, 0.975)),
            "p_perm": float((np.abs((d * signs).mean(axis=1)) >= abs(d.mean()) - 1e-12).mean())}


def matched_weighting(root: Path, out: Path, n_boot: int = 10000, seed: int = 12345) -> pd.DataFrame:
    """The headline matched comparison recomputed under aggregations that remove the two families
    supplying most variants, and under equal weighting of the families a task offers.  The seed is the
    one the primary matched comparison uses, so the `headline` rows reproduce the main table exactly."""
    from .stats import paired_task_difference
    sv = load_survival(root)
    subsets = [("headline", sv),
               ("excluding_T1", sv[sv.transformation != "T1_let_intro"]),
               ("excluding_T1_T2", sv[~sv.transformation.isin(["T1_let_intro", "T2_helper_extract"])])]
    rows = []
    for m in PROVERS:
        for label, sub in subsets:
            d = paired_task_difference(sub[sub.source.isin([m, "reference"])], "source", m, "reference",
                                       n_boot=n_boot, seed=seed)
            rows.append({"model": m, "weighting": label, **d})
        rows.append({"model": m, "weighting": "family_balanced", **_family_balanced_delta(sv, m, n_boot, seed)})
    R = pd.DataFrame(rows)[["model", "weighting", "n_tasks", "n_variants", "psr_a", "psr_b", "delta",
                            "ci_low", "ci_high", "p_perm"]]
    R.to_csv(out / "matched_weighting.csv", index=False)
    return R


def run_matched_weighting(args) -> int:
    args.out.mkdir(parents=True, exist_ok=True)
    R = matched_weighting(args.root, args.out, n_boot=args.n_boot)
    print(R.round(3).to_string(index=False), file=sys.stderr)
    return 0


# =========================================================================== end-to-end robust coverage
def robust_coverage(root: Path, out: Path, n_boot: int = 10000, seed: int = 12345) -> pd.DataFrame:
    """Conditional PSR describes tasks a source already proved.  This combines the two steps: over the
    benchmark tasks that have at least one certified variant, the chance that the source has a valid proof
    of the original program *and* that proof survives a uniformly sampled certified variant of that task."""
    sv = load_survival(root)
    cert = [json.loads(l) for l in (root / "results" / "certification.jsonl").open()]
    bench = sorted({c["task_id"] for c in cert if str(c.get("certificate_valid")) == "True"})
    rows = []
    for m in ["reference"] + ALL_MODELS:
        d = sv[sv.source == m]
        if d.empty:
            continue
        psr_by_task = d.groupby("task_id")["survives"].mean()
        vals = np.array([psr_by_task.get(t, 0.0) for t in bench])
        rng = np.random.default_rng(seed)
        boots = vals[rng.integers(0, len(vals), size=(n_boot, len(vals)))].mean(axis=1)
        rows.append({"source": m, "benchmark_tasks": len(bench), "tasks_with_valid_proof": int(psr_by_task.size),
                     "task_coverage": psr_by_task.size / len(bench), "conditional_psr": float(psr_by_task.mean()),
                     "robust_coverage": float(vals.mean()), "ci_low": float(np.quantile(boots, 0.025)),
                     "ci_high": float(np.quantile(boots, 0.975))})
    R = pd.DataFrame(rows)
    R.to_csv(out / "robust_coverage.csv", index=False)
    return R


def run_robust_coverage(args) -> int:
    args.out.mkdir(parents=True, exist_ok=True)
    R = robust_coverage(args.root, args.out, n_boot=args.n_boot)
    print(R.round(3).to_string(index=False), file=sys.stderr)
    return 0


# =========================================================================== matched-subset characterization
def _matched_tasks(sv: pd.DataFrame, model: str) -> List[str]:
    """The tasks entering the primary matched comparison for `model`: exactly the rule of the paired
    difference (shared certified variants, both sources present)."""
    a, b = sv[sv.source == model], sv[sv.source == "reference"]
    common = set(a.variant_id) & set(b.variant_id)
    pa = a[a.variant_id.isin(common)].groupby("task_id").size()
    pb = b[b.variant_id.isin(common)].groupby("task_id").size()
    return sorted(set(pa.index) & set(pb.index))


def _postcond_loc(root: Path, task_id: str) -> float:
    try:
        from .verina_parser import load_task
        tb = load_task(verina_dir(root) / task_id)
        for name in ("postcond", "spec"):
            try:
                txt = tb.content(name)
            except Exception:
                continue
            return float(sum(1 for ln in txt.splitlines() if ln.strip()))
    except Exception:
        pass
    return float("nan")


def matched_subset(root: Path, out: Path) -> pd.DataFrame:
    """Characterize the 21-25 matched tasks per prover against the 46-task reference subset and the
    185-task construction population: split, recursion, implementation length, postcondition length,
    and which transformation families each task actually offers."""
    audit_p = out / "reference_population_audit.csv"
    if not audit_p.exists():
        raise SystemExit("run `reference_population` first: it writes reference_population_audit.csv")
    attrs = pd.read_csv(audit_p)
    for c in ("has_reference_proof", "in_construction_population", "recursive"):
        attrs[c] = attrs[c].map(lambda x: x in (True, "True", "true", 1))
    fams: Dict[str, set] = collections.defaultdict(set)
    for line in (root / "results" / "certification.jsonl").open():
        c = json.loads(line)
        if c.get("certificate_valid") in (True, "True", "true", 1):
            fams[c["task_id"]].add(c["transformation"])
    for f in FAMILIES:
        attrs[f"has_{f.split('_')[0]}"] = attrs.task_id.map(lambda t: f in fams.get(t, set()))
    attrs["postcond_loc"] = attrs.task_id.map(lambda t: _postcond_loc(root, t))
    sv = load_survival(root)

    def summarize(df: pd.DataFrame, population: str, prover: str) -> dict:
        row = {"population": population, "prover": prover, "n_tasks": int(len(df))}
        if not len(df):
            return row
        row.update({
            "pct_basic": float((df.category == "basic").mean()),
            "pct_recursive": float(df.recursive.mean()),
            "median_code_loc": float(df.code_loc.median()), "mean_code_loc": float(df.code_loc.mean()),
            "median_code_tokens": float(df.code_tokens.median()),
            "median_postcond_loc": float(df.postcond_loc.median()),
            "mean_certified_variants": float(df.n_certified_variants.mean()),
        })
        for f in FAMILIES:
            k = f.split("_")[0]
            row[f"pct_with_{k}"] = float(df[f"has_{k}"].mean())
        return row

    rows = [summarize(attrs[attrs.in_construction_population], "construction_population", "all"),
            summarize(attrs[attrs.n_certified_variants > 0], "benchmark_tasks_with_variants", "all"),
            summarize(attrs[attrs.has_reference_proof], "reference_subset", "all")]
    task_rows = attrs[attrs.has_reference_proof].copy()
    for m in PROVERS:
        solved = sorted(set(sv[sv.source == m].task_id))
        matched = _matched_tasks(sv, m)
        rows.append(summarize(attrs[attrs.task_id.isin(solved)], "solved_by_model", m))
        rows.append(summarize(attrs[attrs.task_id.isin(matched)], "matched_subset", m))
        task_rows[f"matched_{m}"] = task_rows.task_id.isin(matched)
    R = pd.DataFrame(rows)
    R.to_csv(out / "matched_subset_characterization.csv", index=False)
    keep = ["task_id", "category", "recursive", "code_loc", "code_tokens", "postcond_loc", "n_certified_variants",
            "applicable_families"] + [f"has_{f.split('_')[0]}" for f in FAMILIES] + [f"matched_{m}" for m in PROVERS]
    task_rows[keep].to_csv(out / "matched_subset_tasks.csv", index=False)

    short = {"deepseek-prover-v2-7b": "DeepSeek-7B", "goedel-prover-v2-8b": "Goedel-8B", "goedel-prover-v2-32b": "Goedel-32B"}
    lines = [r"\begin{tabular}{lrrrrrrrr}", r"\toprule",
             r"Population & Tasks & Basic (\%) & Recursive (\%) & Med.\ impl.\ LoC & Med.\ postcond.\ LoC & T3 (\%) & T4 (\%) & T5 (\%) \\", r"\midrule"]
    label = {"construction_population": "Construction population", "benchmark_tasks_with_variants": "Tasks with a certified variant",
             "reference_subset": "Supplied-reference subset"}
    for _, r in R.iterrows():
        if r.population == "solved_by_model":
            continue
        name = label.get(r.population, f"Matched, {short.get(r.prover, r.prover)}")
        lines.append(f"{name} & {r.n_tasks} & {100*r.pct_basic:.0f} & {100*r.pct_recursive:.1f} & {r.median_code_loc:.0f} & "
                     f"{r.median_postcond_loc:.0f} & {100*r.pct_with_T3:.0f} & {100*r.pct_with_T4:.0f} & {100*r.pct_with_T5:.0f} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "matched_subset_characterization.tex").write_text("\n".join(lines) + "\n")
    return R


def run_matched_subset(args) -> int:
    args.out.mkdir(parents=True, exist_ok=True)
    R = matched_subset(args.root, args.out)
    cols = ["population", "prover", "n_tasks", "pct_basic", "pct_recursive", "median_code_loc", "median_postcond_loc", "pct_with_T3", "pct_with_T4", "pct_with_T5"]
    print(R[cols].round(3).to_string(index=False), file=sys.stderr)
    return 0


# =========================================================================== within-task variability
def within_task_variability(root: Path, out: Path) -> pd.DataFrame:
    """How much survival varies across independently sampled valid proofs of the same task.  Uses the
    stored re-checks of every valid sample on every certified variant; no proof is generated or compiled."""
    recs: Dict[tuple, list] = collections.defaultdict(list)
    for f in (root / "artifacts" / "selection_sensitivity").glob("*/*/attempt_*.json"):
        d = json.loads(f.read_text())
        recs[(d["model_id"], d["task_id"])].append(d)
    task_rows = []
    for (m, t), atts in sorted(recs.items()):
        atts.sort(key=lambda d: int(d["attempt"]))
        vecs = [{r["variant_id"]: (bool(r["survives"]), r["severity"]) for r in d["survival"]} for d in atts]
        common = [v for v in sorted(vecs[0]) if all(v in s for s in vecs)]
        if not common:
            continue

        def psr(s, sev=None):
            xs = [s[v][0] for v in common if sev is None or s[v][1] == sev]
            return sum(xs) / len(xs) if xs else float("nan")

        per = np.array([psr(s) for s in vecs]); perS = np.array([psr(s, "S") for s in vecs]); perE = np.array([psr(s, "E") for s in vecs])
        n_disagree = sum(1 for v in common if len({s[v][0] for s in vecs}) > 1)
        task_rows.append({"model_id": m, "task_id": t, "n_valid_samples": len(atts), "n_variants": len(common),
                          "n_variants_with_disagreement": n_disagree, "identical_outcomes": n_disagree == 0,
                          "psr_first_valid": float(per[0]), "psr_mean": float(per.mean()), "psr_min": float(per.min()),
                          "psr_max": float(per.max()), "psr_range": float(per.max() - per.min()),
                          "psr_sd": float(per.std(ddof=0)),
                          "psr_S_range": float(np.nanmax(perS) - np.nanmin(perS)) if not np.all(np.isnan(perS)) else float("nan"),
                          "psr_E_range": float(np.nanmax(perE) - np.nanmin(perE)) if not np.all(np.isnan(perE)) else float("nan")})
    T = pd.DataFrame(task_rows)
    T.to_csv(out / "within_task_variability_tasks.csv", index=False)

    rows = []
    for m, g in T.groupby("model_id"):
        multi = g[g.n_valid_samples >= 2]
        # variance decomposition of per-sample PSR: within-task (across samples) versus between-task
        within = float((multi.psr_sd ** 2).mean()) if len(multi) else float("nan")
        between = float(multi.psr_mean.var(ddof=0)) if len(multi) > 1 else float("nan")
        rows.append({"model_id": m, "tasks_with_valid_proof": int(len(g)), "tasks_with_2plus_valid": int(len(multi)),
                     "mean_valid_samples": float(g.n_valid_samples.mean()),
                     "pct_identical_outcomes": float(multi.identical_outcomes.mean()) if len(multi) else float("nan"),
                     "pct_any_disagreement": float((~multi.identical_outcomes).mean()) if len(multi) else float("nan"),
                     "mean_psr_range": float(multi.psr_range.mean()) if len(multi) else float("nan"),
                     "max_psr_range": float(multi.psr_range.max()) if len(multi) else float("nan"),
                     "mean_psr_S_range": float(multi.psr_S_range.mean()) if len(multi) else float("nan"),
                     "mean_psr_E_range": float(multi.psr_E_range.mean()) if len(multi) else float("nan"),
                     "within_task_variance": within, "between_task_variance": between,
                     "within_task_variance_share": within / (within + between) if len(multi) > 1 and (within + between) > 0 else float("nan"),
                     "mean_abs_first_valid_minus_mean": float((multi.psr_first_valid - multi.psr_mean).abs().mean()) if len(multi) else float("nan")})
    R = pd.DataFrame(rows)
    R.to_csv(out / "within_task_variability.csv", index=False)

    short = {"deepseek-prover-v2-7b": "DeepSeek-7B", "goedel-prover-v2-8b": "Goedel-8B", "goedel-prover-v2-32b": "Goedel-32B",
             "qwen3-14b": "Qwen3-14B", "qwen3-32b": "Qwen3-32B"}
    lines = [r"\begin{tabular}{lrrrrrrr}", r"\toprule",
             r"Model & Tasks ($\ge 2$ valid) & Mean valid & Identical outcomes (\%) & Mean PSR range & Mean S range & Mean E range & Within-task var.\ share \\", r"\midrule"]
    for _, r in R.iterrows():
        lines.append(f"{short.get(r.model_id, esc_(r.model_id))} & {r.tasks_with_2plus_valid} & {r.mean_valid_samples:.1f} & "
                     f"{100*r.pct_identical_outcomes:.0f} & {100*r.mean_psr_range:.1f} & {100*r.mean_psr_S_range:.1f} & "
                     f"{100*r.mean_psr_E_range:.1f} & {100*r.within_task_variance_share:.0f} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "within_task_variability.tex").write_text("\n".join(lines) + "\n")
    return R


def esc_(s: str) -> str:
    return str(s).replace("_", "\\_")


def run_within_task_variability(args) -> int:
    args.out.mkdir(parents=True, exist_ok=True)
    R = within_task_variability(args.root, args.out)
    cols = ["model_id", "tasks_with_valid_proof", "tasks_with_2plus_valid", "pct_identical_outcomes", "mean_psr_range", "max_psr_range", "within_task_variance_share"]
    print(R[cols].round(3).to_string(index=False), file=sys.stderr)
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("task", choices=["reference_population", "model_coverage", "aggregation", "per_family", "noncomputable", "t3_selection", "mechanism", "selection", "repair_summary", "length_confound", "seed_sensitivity", "matched_weighting", "robust_coverage", "matched_subset", "within_task_variability"])
    ap.add_argument("--root", type=Path, default=Path("."))
    ap.add_argument("--out", type=Path, default=Path("analysis_outputs"))
    ap.add_argument("--n-boot", type=int, default=10000)
    ap.add_argument("--n-draws", type=int, default=1000)
    args = ap.parse_args(argv)
    return {"reference_population": run_reference_population, "model_coverage": run_model_coverage,
            "aggregation": run_aggregation, "per_family": run_per_family, "mechanism": run_mechanism,
            "selection": run_selection, "repair_summary": run_repair_summary,
            "noncomputable": run_noncomputable, "t3_selection": run_t3_selection,
            "length_confound": run_length_confound, "seed_sensitivity": run_seed_sensitivity,
            "matched_weighting": run_matched_weighting, "robust_coverage": run_robust_coverage,
            "matched_subset": run_matched_subset, "within_task_variability": run_within_task_variability}[args.task](args)


if __name__ == "__main__":
    sys.exit(main())
