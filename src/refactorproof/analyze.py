"""Aggregate raw JSONL outputs into the canonical CSVs and the paper metrics.

Inputs (whatever exists):
  results/candidate_manifest.jsonl, results/variant_manifest.jsonl, results/certification.jsonl,
  results/survival_reference.jsonl, results/survival_models.jsonl, results/model_proofs.jsonl,
  data/verina_audit.csv

Outputs (results/):
  survival_results.csv   candidate_manifest.csv   certification_analysis.csv   main_metrics.csv
  by_severity.csv        by_transformation.csv    by_model.csv                 proof_features.csv
  mechanism_strata.csv   matched_comparison.csv   coverage.csv

Usage::  python -m refactorproof.analyze --results results --data data --verina-root external/verina
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List, Optional

import numpy as np
import pandas as pd

from .proof_features import defined_identifiers, extract_features
from .stats import fast_cluster_bootstrap_psr, paired_task_difference, stratified_psr, variant_level_psr
from .verina_parser import load_task, tier_of


def read_jsonl(p: Path) -> pd.DataFrame:
    if not p.exists():
        return pd.DataFrame()
    rows = [json.loads(ln) for ln in p.read_text().splitlines() if ln.strip()]
    return pd.DataFrame(rows)


def build_survival_table(results: Path, data: Path, verina_root: Path) -> pd.DataFrame:
    cert = read_jsonl(results / "certification.jsonl")
    var = read_jsonl(results / "variant_manifest.jsonl")
    ref = read_jsonl(results / "survival_reference.jsonl")
    mod = read_jsonl(results / "survival_models.jsonl")
    surv = pd.concat([d for d in (ref, mod) if len(d)], ignore_index=True) if (len(ref) or len(mod)) else pd.DataFrame()
    if len(surv) == 0:
        return surv
    surv = surv[surv["outcome"].isin(["survives", "proof_fails"])].copy()  # drop build errors from PSR
    surv["tier"] = surv["task_id"].map(tier_of)
    keep = ["variant_id", "code_loc_original", "code_loc_refactored", "metadata"]
    if len(var):
        surv = surv.merge(var[[c for c in keep if c in var.columns]], on="variant_id", how="left")
    if len(cert):
        surv = surv.merge(cert[["variant_id", "certificate_level", "lean_elapsed_seconds"]].rename(columns={"certificate_level": "cert_level", "lean_elapsed_seconds": "cert_seconds"}), on="variant_id", how="left")
    # proof features (computed on the fixed proof artifact)
    feats = []
    cache: Dict[str, dict] = {}
    for _, r in surv.iterrows():
        key = (r["task_id"], r["proof_source"], r.get("model_id"), r.get("generation_attempt"))
        if key not in cache:
            tb = load_task(verina_root / "datasets" / "verina" / r["task_id"])
            aux_ids = defined_identifiers(tb.content("code_aux")) + defined_identifiers(tb.content("solution_aux"))
            if r["proof_source"] == "reference":
                proof, proof_aux = tb.content("proof"), tb.content("proof_aux")
            else:
                proof, proof_aux = r.get("proof_text", ""), r.get("proof_aux_text", "")
            cache[key] = extract_features(proof, proof_aux, tb.signature.name, aux_ids).to_row()
        f = dict(cache[key])
        f["variant_id"] = r["variant_id"]
        f["_key"] = str(key)
        feats.append(f)
    fdf = pd.DataFrame(feats)
    surv = pd.concat([surv.reset_index(drop=True), fdf.drop(columns=["variant_id"]).reset_index(drop=True)], axis=1)
    surv["group"] = np.where(surv["proof_source"] == "reference", "reference", surv["model_id"].fillna("model"))
    return surv


def coverage_curve(mp: pd.DataFrame, k_max: int = 5) -> pd.DataFrame:
    """Coverage@k per model: fraction of attempted tasks with a Lean-valid sample among attempts 0..k-1."""
    rows = []
    mp = mp.copy()
    mp["_valid"] = mp["original_proof_valid"].fillna(False).astype(bool)
    for m, g in mp.groupby("model_id"):
        n_tasks = g["task_id"].nunique()
        row = {"model_id": m, "tasks_attempted": n_tasks}
        for k in range(1, k_max + 1):
            ok = g[(g["attempt"] < k) & g["_valid"]]["task_id"].nunique()
            row[f"coverage@{k}"] = ok / n_tasks if n_tasks else np.nan
        rows.append(row)
    return pd.DataFrame(rows)


def mechanism_regression(surv: pd.DataFrame, out: Path) -> Optional[pd.DataFrame]:
    """Secondary evidence for the mechanism: logistic regression of variant-level survival on proof-strategy
    indicators, controlling for proof source (model) and severity, with task-clustered standard errors.
    Only meaningful once several proof sources create overlap in strategies; reported as descriptive."""
    try:
        import statsmodels.formula.api as smf
    except ImportError:
        return None
    df = surv.copy()
    df = df[df["outcome"].isin(["survives", "proof_fails"])]
    df = df[df["severity"] != "D"]  # definitional variants are survived by every proof: no information, causes separation
    df["y"] = df["survives"].astype(int)
    df["unfold"] = df["unfolds_target_function"].astype(int)
    df["simp_f"] = df["simp_mentions_target_function"].astype(int)
    df["log_loc"] = np.log1p(pd.to_numeric(df["proof_loc"], errors="coerce").fillna(0))
    df["group"] = df["group"].astype(str)
    df["severity"] = df["severity"].astype(str)
    if df["group"].nunique() < 2 or df["unfold"].nunique() < 2:
        return None
    rows = []
    for name, formula in [
        ("strategy_only", "y ~ unfold + simp_f + log_loc + C(severity)"),
        ("strategy_plus_source", "y ~ C(group, Treatment('reference')) + unfold + simp_f + log_loc + C(severity)"),
    ]:
        try:
            m = smf.logit(formula, data=df).fit(disp=0, cov_type="cluster", cov_kwds={"groups": df["task_id"]})
        except Exception as e:  # separation etc.
            rows.append({"model": name, "term": "ERROR", "coef": np.nan, "se": np.nan, "z": np.nan, "p": np.nan, "note": str(e)[:120]})
            continue
        separated = bool(np.isnan(m.bse).any() or (np.abs(m.params) > 10).any())
        for term in m.params.index:
            rows.append({"model": name, "term": term, "coef": float(m.params[term]), "se": float(m.bse[term]), "z": float(m.tvalues[term]), "p": float(m.pvalues[term]), "n": int(m.nobs), "n_tasks": int(df["task_id"].nunique()), "separated_or_collinear": separated,
                         "note": "coefficients not identifiable (perfect separation / source and strategy collinear)" if separated else ""})
    res = pd.DataFrame(rows)
    res.to_csv(out / "mechanism_regression.csv", index=False)
    return res


def certification_analysis(results: Path, data: Optional[Path] = None) -> pd.DataFrame:
    cand = read_jsonl(results / "candidate_manifest.jsonl")
    cert = read_jsonl(results / "certification.jsonl")
    if len(cand) == 0:
        return pd.DataFrame()
    # restrict denominators to tasks whose ORIGINAL compiles in the pinned environment
    compiling = None
    if data is not None and (data / "verina_audit.csv").exists():
        audit = pd.read_csv(data / "verina_audit.csv")
        if audit["original_compiles"].notna().any():
            compiling = set(audit[audit["original_compiles"].astype(str) == "True"]["task_id"])
    if compiling is not None:
        n_excluded = cand["task_id"].nunique() - len(compiling & set(cand["task_id"]))
        cand = cand[cand["task_id"].isin(compiling)]
        if len(cert):
            cert = cert[cert["task_id"].isin(compiling)]
    else:
        n_excluded = 0
    rows = []
    for t, g in cand.groupby("transformation"):
        sev = g["severity"].iloc[0]
        n_att = len(g)
        n_app = int(g["applicable"].sum())
        n_var = int(g["n_variants"].sum())
        c = cert[cert["transformation"] == t] if len(cert) else pd.DataFrame()
        n_cert_att = len(c)
        n_valid = int(c["certificate_valid"].sum()) if len(c) else 0
        n_rfl = int(c["certificate_closed_by_rfl"].sum()) if len(c) else 0
        fail_cats = c[~c["certificate_valid"].astype(bool)]["certificate_failure_category"].value_counts().to_dict() if len(c) else {}
        rows.append(
            {
                "transformation": t,
                "severity": sev,
                "tasks_attempted": n_att,
                "tasks_applicable": n_app,
                "applicability_rate": n_app / n_att if n_att else np.nan,
                "candidates_generated": n_var,
                "certificates_attempted": n_cert_att,
                "certified": n_valid,
                "certification_rate": n_valid / n_cert_att if n_cert_att else np.nan,
                "certified_rfl": n_rfl,
                "pct_rfl_of_certified": n_rfl / n_valid if n_valid else np.nan,
                "tasks_with_certified_variant": int(c[c["certificate_valid"].astype(bool)]["task_id"].nunique()) if len(c) else 0,
                "failure_categories": json.dumps(fail_cats),
                "tasks_excluded_original_fails": n_excluded,
                "loc_orig_mean_certified": float(pd.to_numeric(g[g["n_variants"] > 0]["code_loc_original"], errors="coerce").mean()) if n_var else np.nan,
            }
        )
    df = pd.DataFrame(rows)
    # selection-bias check: structural stats of certified vs rejected candidates
    if len(cert):
        var = read_jsonl(results / "variant_manifest.jsonl")
        m = cert.merge(var[["variant_id", "code_loc_original", "code_loc_refactored"]], on="variant_id", how="left")
        sel = m.groupby(["transformation", "certificate_valid"]).agg(n=("variant_id", "count"), loc_orig_mean=("code_loc_original", "mean"), loc_orig_median=("code_loc_original", "median")).reset_index()
        sel.to_csv(results / "certification_selection_by_loc.csv", index=False)
    return df


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--results", type=Path, default=Path("results"))
    ap.add_argument("--data", type=Path, default=Path("data"))
    ap.add_argument("--verina-root", type=Path, default=Path("external/verina"))
    ap.add_argument("--n-boot", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=12345)
    args = ap.parse_args(argv)
    R = args.results
    R.mkdir(parents=True, exist_ok=True)

    cand = read_jsonl(R / "candidate_manifest.jsonl")
    if len(cand):
        cand.to_csv(R / "candidate_manifest.csv", index=False)
    ca = certification_analysis(R, args.data)
    if len(ca):
        ca.to_csv(R / "certification_analysis.csv", index=False)
        print(ca.to_string(index=False), file=sys.stderr)

    surv = build_survival_table(R, args.data, args.verina_root)
    if len(surv) == 0:
        print("[analyze] no survival results yet", file=sys.stderr)
        return 0
    surv.to_csv(R / "survival_results.csv", index=False)
    feat_cols = [c for c in surv.columns if c.startswith(("count_", "proof_", "unfolds_", "simp_", "mentions_", "uses_", "target_", "code_aux_identifier", "first_tactic", "n_tactic", "tactic_hist"))]
    surv.drop_duplicates("_key")[["task_id", "proof_source", "model_id", "generation_attempt"] + feat_cols].to_csv(R / "proof_features.csv", index=False)

    # main metrics per group
    main_rows, sev_rows, tr_rows = [], [], []
    for grp, g in surv.groupby("group"):
        est = fast_cluster_bootstrap_psr(g, n_boot=args.n_boot, seed=args.seed)
        row = {"group": grp, "proof_source": g["proof_source"].iloc[0], "n_tasks": est.n_tasks, "n_variants": est.n_variants, "psr_task": est.point, "ci_low": est.ci_low, "ci_high": est.ci_high, "psr_variant": variant_level_psr(g), "implementation_coupling": 1 - est.point}
        for sev in ("D", "S", "E"):
            gs = g[g["severity"] == sev]
            e = fast_cluster_bootstrap_psr(gs, n_boot=args.n_boot, seed=args.seed)
            row[f"psr_{sev}"] = e.point
            row[f"psr_{sev}_ci_low"] = e.ci_low
            row[f"psr_{sev}_ci_high"] = e.ci_high
            row[f"n_tasks_{sev}"] = e.n_tasks
            row[f"n_variants_{sev}"] = e.n_variants
        for rfl in (True, False):
            gr = g[g["certificate_closed_by_rfl"].astype(bool) == rfl]
            e = fast_cluster_bootstrap_psr(gr, n_boot=args.n_boot, seed=args.seed)
            tag = "rfl" if rfl else "nonrfl"
            row[f"psr_{tag}"] = e.point
            row[f"psr_{tag}_ci_low"] = e.ci_low
            row[f"psr_{tag}_ci_high"] = e.ci_high
            row[f"n_variants_{tag}"] = e.n_variants
        main_rows.append(row)
        s = stratified_psr(g, ["severity"], n_boot=args.n_boot, seed=args.seed)
        s.insert(0, "group", grp)
        sev_rows.append(s)
        t = stratified_psr(g, ["transformation", "severity"], n_boot=args.n_boot, seed=args.seed)
        t.insert(0, "group", grp)
        tr_rows.append(t)
    pd.DataFrame(main_rows).to_csv(R / "main_metrics.csv", index=False)
    pd.concat(sev_rows).to_csv(R / "by_severity.csv", index=False)
    pd.concat(tr_rows).to_csv(R / "by_transformation.csv", index=False)
    pd.DataFrame([r for r in main_rows if r["proof_source"] != "reference"]).to_csv(R / "by_model.csv", index=False)

    # mechanism strata
    strata = []
    for col in ("unfolds_target_function", "simp_mentions_target_function", "uses_automation", "mentions_code_aux_identifier"):
        s = stratified_psr(surv, ["group", col], n_boot=args.n_boot, seed=args.seed)
        s = s.rename(columns={col: "stratum_value"})
        s.insert(1, "stratum", col)
        strata.append(s)
        s2 = stratified_psr(surv, ["group", "severity", col], n_boot=args.n_boot, seed=args.seed).rename(columns={col: "stratum_value"})
        s2.insert(1, "stratum", col)
        strata.append(s2)
    pd.concat(strata).to_csv(R / "mechanism_strata.csv", index=False)

    # matched LLM vs reference on exactly matched (task, variant)
    matched = []
    if (surv["proof_source"] == "reference").any():
        for grp in sorted(set(surv["group"]) - {"reference"}):
            sub = surv[surv["group"].isin([grp, "reference"])]
            d = paired_task_difference(sub, "group", grp, "reference", n_boot=args.n_boot, seed=args.seed)
            d.update({"model": grp, "stratum": "all", "stratum_value": ""})
            matched.append(d)
            for col in ("unfolds_target_function", "severity"):
                for val, sv in sub.groupby(col):
                    dd = paired_task_difference(sv, "group", grp, "reference", n_boot=args.n_boot, seed=args.seed)
                    dd.update({"model": grp, "stratum": col, "stratum_value": str(val)})
                    matched.append(dd)
    if matched:
        pd.DataFrame(matched).to_csv(R / "matched_comparison.csv", index=False)

    # Experiment B: within-model strategy conditions (same base model, same tasks, different prompt condition)
    strat_rows = []
    if "strategy_condition" in surv.columns and "base_model" in surv.columns:
        msurv = surv[surv["proof_source"] != "reference"]
        for base, gb in msurv.groupby("base_model"):
            conds = sorted(set(gb["strategy_condition"].dropna()))
            if len(conds) < 2:
                continue
            # orientation: condition_a = intervention, condition_b = baseline ("default"), so delta = intervention - natural;
            # intervention-vs-intervention pairs follow in alphabetical order
            pairs = [(c, "default") for c in conds if c != "default" and "default" in conds]
            others = [c for c in conds if c != "default"]
            pairs += [(a, b) for i, a in enumerate(others) for b in others[i + 1:]]
            for c1, c2 in pairs:
                if True:
                    sub = gb[gb["strategy_condition"].isin([c1, c2])]
                    d = paired_task_difference(sub, "strategy_condition", c1, c2, n_boot=args.n_boot, seed=args.seed)
                    d.update({"base_model": base, "condition_a": c1, "condition_b": c2, "stratum": "all", "stratum_value": ""})
                    strat_rows.append(d)
                    for val, sv in sub.groupby("severity"):
                        dd = paired_task_difference(sv, "strategy_condition", c1, c2, n_boot=args.n_boot, seed=args.seed)
                        dd.update({"base_model": base, "condition_a": c1, "condition_b": c2, "stratum": "severity", "stratum_value": str(val)})
                        strat_rows.append(dd)
    if strat_rows:
        sdf = pd.DataFrame(strat_rows)
        # interaction: does the condition effect differ between structural and semantic variants?
        # per task: (PSR_a - PSR_b on E) - (PSR_a - PSR_b on S), bootstrap over tasks with both severities
        inter = []
        for (base, c1, c2), g in sdf.groupby(["base_model", "condition_a", "condition_b"]):
            sub = msurv[(msurv["base_model"] == base) & (msurv["strategy_condition"].isin([c1, c2]))]
            per = sub.groupby(["task_id", "strategy_condition", "severity"])["survives"].mean().unstack(["strategy_condition", "severity"])
            try:
                dS = per[(c1, "S")] - per[(c2, "S")]
                dE = per[(c1, "E")] - per[(c2, "E")]
            except KeyError:
                continue
            dd = (dE - dS).dropna()
            if len(dd) < 3:
                continue
            rng = np.random.default_rng(args.seed)
            boots = [dd.sample(len(dd), replace=True, random_state=int(rng.integers(1 << 31))).mean() for _ in range(min(args.n_boot, 5000))]
            signs = [(dd * rng.choice([-1, 1], size=len(dd))).mean() for _ in range(min(args.n_boot, 5000))]
            p_perm = float(np.mean(np.abs(signs) >= abs(dd.mean())))
            inter.append({"base_model": base, "condition_a": c1, "condition_b": c2, "n_tasks": int(len(dd)), "delta_E_minus_delta_S": float(dd.mean()), "ci_low": float(np.percentile(boots, 2.5)), "ci_high": float(np.percentile(boots, 97.5)), "p_perm": p_perm})
        # pooled interaction across base models for the same condition pair (per-task Gamma concatenated)
        pooled_rows = []
        pairs_seen = {(r["condition_a"], r["condition_b"]) for r in inter}
        for c1, c2 in pairs_seen:
            gs = []
            for base, gb in msurv.groupby("base_model"):
                sub = gb[gb["strategy_condition"].isin([c1, c2])]
                per = sub.groupby(["task_id", "strategy_condition", "severity"])["survives"].mean().unstack(["strategy_condition", "severity"])
                try:
                    gs.append(((per[(c1, "E")] - per[(c2, "E")]) - (per[(c1, "S")] - per[(c2, "S")])).dropna())
                except KeyError:
                    continue
            if len(gs) >= 2:
                dd = pd.concat(gs)
                rng = np.random.default_rng(args.seed)
                boots = [dd.sample(len(dd), replace=True, random_state=int(rng.integers(1 << 31))).mean() for _ in range(min(args.n_boot, 5000))]
                signs = [(dd * rng.choice([-1, 1], size=len(dd))).mean() for _ in range(min(args.n_boot, 5000))]
                pooled_rows.append({"base_model": "pooled", "condition_a": c1, "condition_b": c2, "n_tasks": int(len(dd)), "delta_E_minus_delta_S": float(dd.mean()), "ci_low": float(np.percentile(boots, 2.5)), "ci_high": float(np.percentile(boots, 97.5)), "p_perm": float(np.mean(np.abs(signs) >= abs(dd.mean())))})
        inter += pooled_rows
        if inter:
            pd.DataFrame(inter).to_csv(R / "strategy_interaction.csv", index=False)
        sdf.to_csv(R / "strategy_comparison.csv", index=False)

    # secondary: regression of survival on strategy indicators, controlling for source and severity
    reg = mechanism_regression(surv, R)
    if reg is not None:
        keep = reg[reg["term"].isin(["unfold", "simp_f", "log_loc"])]
        print(keep.to_string(index=False), file=sys.stderr)

    # coverage per model
    mp = read_jsonl(R / "model_proofs.jsonl")
    if len(mp):
        mp["_valid"] = mp["original_proof_valid"].fillna(False).astype(bool)
        per_task = mp.groupby(["model_id", "task_id"]).agg(any_valid=("_valid", "any"), frac_valid=("_valid", "mean"), n=("_valid", "size")).reset_index()
        cov = per_task.groupby("model_id").agg(tasks_attempted=("task_id", "nunique"), tasks_valid=("any_valid", "sum"), mean_frac_valid_samples=("frac_valid", "mean")).reset_index()
        cov["tasks_valid"] = cov["tasks_valid"].astype(int)
        cov["coverage"] = cov["tasks_valid"] / cov["tasks_attempted"]  # tasks with >=1 Lean-valid sample (= tasks with a primary proof)
        cov["valid_samples"] = mp.groupby("model_id")["_valid"].sum().reindex(cov["model_id"]).values.astype(int)
        cov["n_samples"] = mp.groupby("model_id").size().reindex(cov["model_id"]).values
        coverage_curve(mp, k_max=int(mp["attempt"].max()) + 1 if len(mp) else 5).to_csv(R / "coverage_curve.csv", index=False)
        cov.to_csv(R / "coverage.csv", index=False)

    print(pd.DataFrame(main_rows)[["group", "n_tasks", "n_variants", "psr_task", "ci_low", "ci_high", "psr_D", "psr_S", "psr_E", "psr_rfl", "psr_nonrfl"]].to_string(index=False), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
