"""Render paper tables (LaTeX) and figures directly from the analysis CSVs.

Usage::  python -m refactorproof.make_tables --results results --out paper_artifacts

Tables
  table1_benchmark_construction.tex   applicability / certification / rfl share per transformation
  table2_main_psr.tex                 task-normalized PSR with CIs, by D/S/E, per proof source
  table3_tactic_profile.tex           mechanism / tactic profile per proof source
  table4_matched.tex                  matched LLM-vs-reference ΔPSR (+ unfold strata)
Figures
  fig2_psr_by_severity.pdf            PSR across D→S→E with task-cluster CIs
  fig3_mechanism.pdf                  PSR stratified by unfolds_target_function
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import List, Optional

import numpy as np
import pandas as pd

SEV_ORDER = ["D", "S", "E"]
SEV_LABEL = {"D": "D (definitional)", "S": "S (structural)", "E": "E (semantic)"}


def esc(s):
    return str(s).replace("_", "\\_")


def pct(x, d=1):
    return "--" if pd.isna(x) else f"{100*x:.{d}f}"


def ci(lo, hi, d=1):
    return "--" if pd.isna(lo) else f"[{100*lo:.{d}f}, {100*hi:.{d}f}]"


def _complete_groups(R: Path):
    """Model groups whose generation run attempted every task (partial/in-progress runs are excluded from tables)."""
    cov_path = R / "coverage.csv"
    if not cov_path.exists():
        return None
    cov = pd.read_csv(cov_path)
    full = int(cov["tasks_attempted"].max())
    return set(cov[cov["tasks_attempted"] >= full]["model_id"]) | {"reference"}


def table1(R: Path, out: Path):
    df = pd.read_csv(R / "certification_analysis.csv")
    lines = [r"\begin{tabular}{llrrrrrr}", r"\toprule", r"Transformation & Sev. & Applicable tasks & Candidates & Certified & Cert. rate (\%) & rfl (\%) & Tasks w/ variant \\", r"\midrule"]
    for _, r in df.sort_values("severity", key=lambda s: s.map({"D": 0, "S": 1, "E": 2})).iterrows():
        lines.append(f"{esc(r.transformation)} & {r.severity} & {int(r.tasks_applicable)}/{int(r.tasks_attempted)} & {int(r.candidates_generated)} & {int(r.certified)} & {pct(r.certification_rate)} & {pct(r.pct_rfl_of_certified)} & {int(r.tasks_with_certified_variant)} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "table1_benchmark_construction.tex").write_text("\n".join(lines) + "\n")


def table2(R: Path, out: Path):
    df = pd.read_csv(R / "main_metrics.csv")
    ok = _complete_groups(R)
    if ok is not None:
        df = df[df["group"].isin(ok)]
    df = df[~df["group"].astype(str).str.contains("__")]  # strategy/prompt conditions live in the strategy tables
    lines = [r"\begin{tabular}{lrrlrrr}", r"\toprule", r"Proof source & Tasks & Variants & PSR$_{task}$ (\%) [95\% CI] & D & S & E \\", r"\midrule"]
    for _, r in df.iterrows():
        lines.append(f"{esc(r.group)} & {int(r.n_tasks)} & {int(r.n_variants)} & {pct(r.psr_task)} {ci(r.ci_low, r.ci_high)} & {pct(r.psr_D)} & {pct(r.psr_S)} & {pct(r.psr_E)} \\\\")
    lines += [r"\midrule", r"\multicolumn{7}{l}{\small rfl-certified vs.\ non-rfl variants:} \\"]
    for _, r in df.iterrows():
        lines.append(f"{esc(r.group)} & & & rfl: {pct(r.psr_rfl)} {ci(r.psr_rfl_ci_low, r.psr_rfl_ci_high)} & \\multicolumn{{3}}{{l}}{{non-rfl: {pct(r.psr_nonrfl)} {ci(r.psr_nonrfl_ci_low, r.psr_nonrfl_ci_high)}}} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "table2_main_psr.tex").write_text("\n".join(lines) + "\n")


def table3(R: Path, out: Path):
    pf = pd.read_csv(R / "proof_features.csv")
    if "group" not in pf.columns:
        pf = pf.copy(); pf["group"] = pf.apply(lambda r: "reference" if r["proof_source"] == "reference" else r.get("model_id"), axis=1)
    ok = _complete_groups(R)
    if ok is not None:
        pf = pf[pf["group"].isin(ok)]
    pf = pf[~pf["group"].astype(str).str.contains("__")]  # base models only; conditions are in the strategy tables
    pf["group"] = np.where(pf["proof_source"] == "reference", "reference", pf["model_id"].fillna("model"))
    rows = []
    for g, d in pf.groupby("group"):
        rows.append({
            "group": g, "n": len(d),
            "unfold_target": d["unfolds_target_function"].mean(),
            "simp_target": d["simp_mentions_target_function"].mean(),
            "automation": d["uses_automation"].mean(),
            "aux_ident": d["mentions_code_aux_identifier"].mean(),
            "median_loc": d["proof_loc"].median(),
            "median_tactics": d["n_tactic_tokens"].median(),
            "median_rw": d["count_rw"].median(),
            "median_have": d["count_have"].median(),
        })
    t = pd.DataFrame(rows)
    lines = [r"\begin{tabular}{lrrrrrrrr}", r"\toprule", r"Proof source & $n$ & unfold target (\%) & simp[target] (\%) & automation (\%) & mentions aux id (\%) & med. LoC & med. tactics & med. rw \\", r"\midrule"]
    for _, r in t.iterrows():
        lines.append(f"{esc(r.group)} & {int(r.n)} & {pct(r.unfold_target)} & {pct(r.simp_target)} & {pct(r.automation)} & {pct(r.aux_ident)} & {r.median_loc:.0f} & {r.median_tactics:.0f} & {r.median_rw:.0f} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "table3_tactic_profile.tex").write_text("\n".join(lines) + "\n")
    t.to_csv(out / "table3_tactic_profile.csv", index=False)


def table4(R: Path, out: Path):
    p = R / "matched_comparison.csv"
    if not p.exists():
        return
    df = pd.read_csv(p)
    ok = _complete_groups(R)
    if ok is not None:
        df = df[df["model"].isin(ok)]
    df = df[~df["model"].astype(str).str.contains("__")]
    lines = [r"\begin{tabular}{llrrrrrr}", r"\toprule", r"Model & Stratum & Matched tasks & Ref.\ PSR & LLM PSR & $\Delta$PSR & 95\% CI & $p$ \\", r"\midrule"]
    for _, r in df.iterrows():
        if not r.n_tasks or pd.isna(r.delta):
            continue  # empty stratum (e.g. no model proof unfolds the target)
        strat = "all" if r.stratum == "all" else esc(f"{r.stratum}={r.stratum_value}")
        lines.append(f"{esc(r.model)} & {strat} & {int(r.n_tasks)} & {pct(r.psr_b)} & {pct(r.psr_a)} & {100*r.delta:+.1f} & {ci(r.ci_low, r.ci_high)} & {r.p_perm:.3f} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "table4_matched.tex").write_text("\n".join(lines) + "\n")


def table5(R: Path, out: Path):
    """Experiment B: per-condition coverage, manipulation check and PSR, plus paired deltas vs the neutral control."""
    mp_path, pf_path, mm_path = R / "coverage.csv", R / "proof_features.csv", R / "main_metrics.csv"
    if not (mp_path.exists() and pf_path.exists() and mm_path.exists()):
        return
    cov = pd.read_csv(mp_path).set_index("model_id")
    pf = pd.read_csv(pf_path)
    if "group" not in pf.columns:
        pf = pf.copy(); pf["group"] = pf.apply(lambda r: "reference" if r["proof_source"] == "reference" else r.get("model_id"), axis=1)
    mm = pd.read_csv(mm_path).set_index("group")
    ok = _complete_groups(R)
    groups = [g for g in mm.index if g != "reference" and (ok is None or g in ok)]
    bases = sorted({g.split("__")[0] for g in groups if "__" in g})
    if not bases:
        return
    sc = pd.read_csv(R / "strategy_comparison.csv") if (R / "strategy_comparison.csv").exists() else pd.DataFrame()
    lines = [r"\begin{tabular}{llrrrrrrr}", r"\toprule", r"Model & Condition & Coverage@5 & unfold $f$ (\%) & simp[$f$] (\%) & PSR$_{task}$ & D & S & E \\", r"\midrule"]
    for base in bases:
        conds = [base] + sorted(g for g in groups if g.startswith(base + "__"))
        for g in conds:
            if g not in mm.index:
                continue
            m = mm.loc[g]; f = pf[pf["group"] == g]
            cname = "neutral (base run)" if g == base else g.split("__", 1)[1].replace("_", " ")
            c5 = cov.loc[g, "coverage"] if g in cov.index else float("nan")
            lines.append(f"{esc(base)} & {esc(cname)} & {100*c5:.1f} & {100*f['unfolds_target_function'].mean():.0f} & {100*f['simp_mentions_target_function'].mean():.0f} & {pct(m.psr_task)} & {pct(m.psr_D)} & {pct(m.psr_S)} & {pct(m.psr_E)} \\\\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    (out / "table5_strategy_conditions.tex").write_text("\n".join(lines) + "\n")
    if len(sc):
        l2 = [r"\begin{tabular}{lllrrrrrr}", r"\toprule", r"Model & Condition A & Condition B & Stratum & Paired tasks & PSR A & PSR B & $\Delta$(A$-$B) [95\% CI] & $p$ \\", r"\midrule"]
        for _, r in sc.iterrows():
            if not r.n_tasks or pd.isna(r.delta):
                continue
            if ok is not None and not all((f"{r.base_model}__{c}" in ok) or c == "default" for c in (r.condition_a, r.condition_b)):
                continue
            strat = "all" if r.stratum == "all" else f"severity={r.stratum_value}"
            l2.append(f"{esc(r.base_model)} & {esc(str(r.condition_a).replace('_',' '))} & {esc(str(r.condition_b).replace('_',' '))} & {strat} & {int(r.n_tasks)} & {pct(r.psr_a)} & {pct(r.psr_b)} & {100*r.delta:+.1f} {ci(r.ci_low, r.ci_high)} & {r.p_perm:.3f} \\\\")
        l2 += [r"\bottomrule", r"\end{tabular}"]
        (out / "table6_strategy_paired.tex").write_text("\n".join(l2) + "\n")


def figures(R: Path, out: Path):
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    sev = pd.read_csv(R / "by_severity.csv")
    groups = list(dict.fromkeys(sev["group"]))
    fig, ax = plt.subplots(figsize=(4.2, 2.8))
    w = 0.8 / max(len(groups), 1)
    for i, g in enumerate(groups):
        d = sev[sev.group == g].set_index("severity").reindex(SEV_ORDER)
        x = np.arange(len(SEV_ORDER)) + (i - (len(groups) - 1) / 2) * w
        y = 100 * d["psr_task"].to_numpy()
        lo = 100 * (d["psr_task"] - d["ci_low"]).to_numpy()
        hi = 100 * (d["ci_high"] - d["psr_task"]).to_numpy()
        ax.bar(x, y, width=w * 0.95, yerr=[np.nan_to_num(lo), np.nan_to_num(hi)], capsize=2, label=g)
        for xi, yi, n in zip(x, y, d["n_variants"]):
            if not np.isnan(yi):
                ax.text(xi, min(yi + 3, 97), f"n={int(n)}", ha="center", fontsize=6)
    ax.set_xticks(range(len(SEV_ORDER)))
    ax.set_xticklabels([SEV_LABEL[s] for s in SEV_ORDER], fontsize=8)
    ax.set_ylabel("Task-normalized PSR (%)")
    ax.set_ylim(0, 105)
    ax.legend(fontsize=7, frameon=False)
    fig.tight_layout()
    fig.savefig(out / "fig2_psr_by_severity.pdf")
    fig.savefig(out / "fig2_psr_by_severity.png", dpi=200)

    ms = pd.read_csv(R / "mechanism_strata.csv")
    m = ms[(ms.stratum == "unfolds_target_function") & ms["severity"].isna()] if "severity" in ms.columns else ms[ms.stratum == "unfolds_target_function"]
    if len(m):
        fig, ax = plt.subplots(figsize=(4.2, 2.8))
        groups = list(dict.fromkeys(m["group"]))
        w = 0.8 / max(len(groups), 1)
        for i, g in enumerate(groups):
            d = m[m.group == g]
            xs, ys, los, his, ns = [], [], [], [], []
            for j, val in enumerate([False, True]):
                r = d[d["stratum_value"].astype(str) == str(val)]
                xs.append(j + (i - (len(groups) - 1) / 2) * w)
                ys.append(100 * r["psr_task"].iloc[0] if len(r) else np.nan)
                los.append(100 * (r["psr_task"].iloc[0] - r["ci_low"].iloc[0]) if len(r) else 0)
                his.append(100 * (r["ci_high"].iloc[0] - r["psr_task"].iloc[0]) if len(r) else 0)
                ns.append(int(r["n_variants"].iloc[0]) if len(r) else 0)
            ax.bar(xs, np.nan_to_num(ys), width=w * 0.95, yerr=[los, his], capsize=2, label=g)
            for xi, yi, n in zip(xs, ys, ns):
                if n:
                    ax.text(xi, min((yi if not np.isnan(yi) else 0) + 3, 97), f"n={n}", ha="center", fontsize=6)
        ax.set_xticks([0, 1])
        ax.set_xticklabels(["no unfold of target", "unfolds target"], fontsize=8)
        ax.set_ylabel("Task-normalized PSR (%)")
        ax.set_ylim(0, 105)
        ax.legend(fontsize=7, frameon=False)
        fig.tight_layout()
        fig.savefig(out / "fig3_mechanism.pdf")
        fig.savefig(out / "fig3_mechanism.png", dpi=200)


_WORDS = {"1": "one", "2": "two", "3": "three", "4": "four", "5": "five"}


def _galias(group: str) -> str:
    """Macro-safe alias for a group: reference -> Ref, goedel-prover-v2-8b -> Goedel, qwen3-14b -> Qwen."""
    if group == "reference":
        return "Ref"
    g = str(group)
    base, _, cond = g.partition("__")          # strategy conditions: goedel-prover-v2-8b__avoid_unfold -> GoedelAvoidunfold
    head = re.split(r"[-_]", base)[0]
    head = re.sub(r"\d+", "", head)
    alias = head[:1].upper() + head[1:].lower()
    if base.endswith("32b"):
        alias += "XXXII"                        # size suffix without digits (macro-safe)
    if cond:
        alias += re.sub(r"[^A-Za-z]", "", cond.title())
    return alias


def _tag(transformation: str) -> str:
    """T1_let_intro -> Tone (LaTeX macro names cannot contain digits)."""
    t = transformation.split("_")[0]
    return "".join(_WORDS.get(ch, ch) for ch in t)


def numbers(R: Path, out: Path):
    """LaTeX macros with headline numbers so prose stays in sync with the CSVs."""
    lines = []
    def m(name, val):
        lines.append(f"\\newcommand{{\\{name}}}{{{val}}}")
    ca = pd.read_csv(R / "certification_analysis.csv")
    m("nTasks", 189)
    m("nCompiling", int(189 - ca["tasks_excluded_original_fails"].iloc[0]) if "tasks_excluded_original_fails" in ca else 185)
    m("nCandidates", int(ca["candidates_generated"].sum()))
    m("nCertified", int(ca["certified"].sum()))
    m("nCertifiedRfl", int(ca["certified_rfl"].sum()))
    for _, r in ca.iterrows():
        tag = _tag(r.transformation)
        m(f"cert{tag}", f"{int(r.certified)}/{int(r.candidates_generated)}")
        m(f"certRate{tag}", f"{100*r.certification_rate:.0f}")
        m(f"appl{tag}", int(r.tasks_applicable))
    mm = pd.read_csv(R / "main_metrics.csv")
    for _, r in mm.iterrows():
        g = _galias(r.group)
        m(f"psr{g}", f"{100*r.psr_task:.1f}")
        m(f"psr{g}CI", f"[{100*r.ci_low:.1f}, {100*r.ci_high:.1f}]")
        for sev in ("D", "S", "E"):
            m(f"psr{g}{sev}", f"{100*r[f'psr_{sev}']:.1f}")
        m(f"nTasks{g}", int(r.n_tasks)); m(f"nVariants{g}", int(r.n_variants))
    bt = pd.read_csv(R / "by_transformation.csv")
    for _, r in bt.iterrows():
        g = _galias(r.group)
        tag = _tag(r.transformation)
        m(f"psr{g}{tag}", f"{100*r.psr_task:.1f}")
        m(f"n{g}{tag}", int(r.n_variants))
    if (R / "matched_comparison.csv").exists():
        mc = pd.read_csv(R / "matched_comparison.csv")
        for _, r in mc.iterrows():
            if not r.n_tasks or pd.isna(r.delta):
                continue
            g = _galias(r.model)
            st = "All" if r.stratum == "all" else ("Sev" + str(r.stratum_value) if r.stratum == "severity" else ("Unfold" + ("Yes" if str(r.stratum_value) == "True" else "No")))
            # psr_a is the model, psr_b the reference (delta = a - b), matching table4's column order
            m(f"matchedN{g}{st}", int(r.n_tasks)); m(f"matchedRef{g}{st}", f"{100*r.psr_b:.1f}"); m(f"matchedModel{g}{st}", f"{100*r.psr_a:.1f}")
            m(f"delta{g}{st}", f"{100*r.delta:+.1f}"); m(f"delta{g}{st}CI", f"[{100*r.ci_low:.1f}, {100*r.ci_high:.1f}]"); m(f"pperm{g}{st}", f"{r.p_perm:.3f}")
    if (R / "strategy_comparison.csv").exists():
        sc = pd.read_csv(R / "strategy_comparison.csv")
        for _, r in sc.iterrows():
            if not r.n_tasks or pd.isna(r.delta):
                continue
            g = _galias(r.base_model); ca = re.sub(r"[^A-Za-z]", "", str(r.condition_a).title()); cb = re.sub(r"[^A-Za-z]", "", str(r.condition_b).title())
            st = "All" if r.stratum == "all" else "Sev" + str(r.stratum_value)
            key = f"{g}{ca}Vs{cb}{st}"
            m(f"stratN{key}", int(r.n_tasks)); m(f"stratA{key}", f"{100*r.psr_a:.1f}"); m(f"stratB{key}", f"{100*r.psr_b:.1f}")
            m(f"stratDelta{key}", f"{100*r.delta:+.1f}"); m(f"stratDelta{key}CI", f"[{100*r.ci_low:.1f}, {100*r.ci_high:.1f}]"); m(f"stratP{key}", f"{r.p_perm:.3f}")
    if (R / "strategy_interaction.csv").exists():
        si = pd.read_csv(R / "strategy_interaction.csv")
        for _, r in si.iterrows():
            g = _galias(r.base_model); ca = re.sub(r"[^A-Za-z]", "", str(r.condition_a).title()); cb = re.sub(r"[^A-Za-z]", "", str(r.condition_b).title())
            key = f"{g}{ca}Vs{cb}"
            m(f"interN{key}", int(r.n_tasks)); m(f"interDelta{key}", f"{100*r.delta_E_minus_delta_S:+.1f}"); m(f"interDelta{key}CI", f"[{100*r.ci_low:.1f}, {100*r.ci_high:.1f}]"); m(f"interP{key}", f"{r.p_perm:.3f}")
    try:
        from .make_tables_extra import extra_macros
    except ImportError:
        pass
    else:
        extra_macros(R, m)
    if (R / "coverage.csv").exists():
        cv = pd.read_csv(R / "coverage.csv")
        for _, r in cv.iterrows():
            g = _galias(r.model_id)
            m(f"coverage{g}", f"{int(r.tasks_valid)}/{int(r.tasks_attempted)}"); m(f"coveragePct{g}", f"{100*r.coverage:.1f}")
    pf = pd.read_csv(R / "proof_features.csv")
    ref = pf[pf.proof_source == "reference"]
    if len(ref):
        m("refUnfoldPct", f"{100*ref['unfolds_target_function'].mean():.0f}")
        m("refMedianLoc", int(ref["proof_loc"].median()))
    if "group" not in pf.columns and "proof_source" in pf.columns:
        pf = pf.copy()
        pf["group"] = pf.apply(lambda r: "reference" if r["proof_source"] == "reference" else r.get("model_id"), axis=1)
    if "group" in pf.columns:
        for g, sub in pf.groupby("group"):
            a = _galias(g)
            m(f"unfoldPct{a}", f"{100*sub['unfolds_target_function'].mean():.0f}")
            m(f"simpTargetPct{a}", f"{100*sub['simp_mentions_target_function'].mean():.0f}")
            m(f"medianLoc{a}", int(sub["proof_loc"].median()))
    (out / "numbers.tex").write_text("\n".join(lines) + "\n")


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--results", type=Path, default=Path("results"))
    ap.add_argument("--out", type=Path, default=Path("paper_artifacts"))
    args = ap.parse_args(argv)
    (args.out / "tables").mkdir(parents=True, exist_ok=True)
    (args.out / "figures").mkdir(parents=True, exist_ok=True)
    if (args.results / "certification_analysis.csv").exists():
        table1(args.results, args.out / "tables")
    if (args.results / "main_metrics.csv").exists():
        table2(args.results, args.out / "tables")
        table3(args.results, args.out / "tables")
        table4(args.results, args.out / "tables")
        table5(args.results, args.out / "tables")
        try:
            from .make_tables_extra import extra_tables
        except ImportError:
            pass
        else:
            extra_tables(args.results, args.out / "tables")
        figures(args.results, args.out / "figures")
        numbers(args.results, args.out / "tables")
    print(f"[make_tables] wrote {sorted(p.name for p in (args.out / 'tables').iterdir())} and {sorted(p.name for p in (args.out / 'figures').iterdir())}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
