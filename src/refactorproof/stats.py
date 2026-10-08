"""Task-clustered statistics for PSR-type metrics.

Variants derived from the same source task are not independent, so every
uncertainty estimate here resamples *tasks* (clusters) with replacement and
keeps all variants of each sampled task.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple

import numpy as np
import pandas as pd


@dataclass
class Estimate:
    point: float
    ci_low: float
    ci_high: float
    n_tasks: int
    n_variants: int
    n_replicates: int

    def fmt(self, pct: bool = True, digits: int = 1) -> str:
        if np.isnan(self.point):
            return "–"
        if pct:
            return f"{100*self.point:.{digits}f} [{100*self.ci_low:.{digits}f}, {100*self.ci_high:.{digits}f}]"
        return f"{self.point:.3f} [{self.ci_low:.3f}, {self.ci_high:.3f}]"


def task_normalized_psr(df: pd.DataFrame, task_col: str = "task_id", y_col: str = "survives") -> float:
    """Mean over tasks of the per-task survival fraction (primary aggregate)."""
    if len(df) == 0:
        return float("nan")
    per_task = df.groupby(task_col)[y_col].mean()
    return float(per_task.mean())


def variant_level_psr(df: pd.DataFrame, y_col: str = "survives") -> float:
    return float(df[y_col].mean()) if len(df) else float("nan")


def cluster_bootstrap(
    df: pd.DataFrame,
    stat: Callable[[pd.DataFrame], float],
    task_col: str = "task_id",
    n_boot: int = 10000,
    seed: int = 12345,
    ci: float = 0.95,
) -> Estimate:
    tasks = df[task_col].unique()
    n = len(tasks)
    point = stat(df)
    if n == 0:
        return Estimate(float("nan"), float("nan"), float("nan"), 0, 0, 0)
    rng = np.random.default_rng(seed)
    groups = {t: g for t, g in df.groupby(task_col)}
    # precompute per-task arrays for speed when stat is task-normalized PSR
    vals = np.empty(n_boot)
    for b in range(n_boot):
        sample = rng.choice(tasks, size=n, replace=True)
        boot = pd.concat([groups[t] for t in sample], ignore_index=True)
        # duplicate tasks must be treated as distinct clusters: relabel
        boot = boot.copy()
        boot[task_col] = np.repeat(np.arange(n), [len(groups[t]) for t in sample])
        vals[b] = stat(boot)
    alpha = (1 - ci) / 2
    lo, hi = np.nanquantile(vals, [alpha, 1 - alpha])
    return Estimate(point, float(lo), float(hi), int(n), int(len(df)), n_boot)


def fast_cluster_bootstrap_psr(df: pd.DataFrame, task_col: str = "task_id", y_col: str = "survives", n_boot: int = 10000, seed: int = 12345, ci: float = 0.95) -> Estimate:
    """Vectorised cluster bootstrap for the task-normalized PSR."""
    if len(df) == 0:
        return Estimate(float("nan"), float("nan"), float("nan"), 0, 0, 0)
    per_task = df.groupby(task_col)[y_col].mean().to_numpy(dtype=float)
    n = len(per_task)
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, n, size=(n_boot, n))
    vals = per_task[idx].mean(axis=1)
    alpha = (1 - ci) / 2
    lo, hi = np.quantile(vals, [alpha, 1 - alpha])
    return Estimate(float(per_task.mean()), float(lo), float(hi), n, int(len(df)), n_boot)


def paired_task_difference(
    df: pd.DataFrame,
    group_col: str,
    a: str,
    b: str,
    task_col: str = "task_id",
    y_col: str = "survives",
    n_boot: int = 10000,
    seed: int = 12345,
    ci: float = 0.95,
    n_perm: int = 10000,
) -> Dict:
    """Mean over matched tasks of PSR_a(task) - PSR_b(task) on exactly matched variants,
    with task-cluster bootstrap CI and a paired sign-flip permutation p-value."""
    da = df[df[group_col] == a]
    db = df[df[group_col] == b]
    common_variants = set(da["variant_id"]) & set(db["variant_id"])
    da = da[da["variant_id"].isin(common_variants)]
    db = db[db["variant_id"].isin(common_variants)]
    pa = da.groupby(task_col)[y_col].mean()
    pb = db.groupby(task_col)[y_col].mean()
    tasks = sorted(set(pa.index) & set(pb.index))
    if not tasks:
        return {"n_tasks": 0, "n_variants": 0, "psr_a": float("nan"), "psr_b": float("nan"), "delta": float("nan"), "ci_low": float("nan"), "ci_high": float("nan"), "p_perm": float("nan")}
    d = np.array([pa[t] - pb[t] for t in tasks])
    n = len(d)
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, n, size=(n_boot, n))
    boots = d[idx].mean(axis=1)
    alpha = (1 - ci) / 2
    lo, hi = np.quantile(boots, [alpha, 1 - alpha])
    signs = rng.choice([-1.0, 1.0], size=(n_perm, n))
    perm = (d * signs).mean(axis=1)
    p = float((np.abs(perm) >= abs(d.mean()) - 1e-12).mean())
    return {
        "n_tasks": n,
        "n_variants": int(len(common_variants)),
        "psr_a": float(np.mean([pa[t] for t in tasks])),
        "psr_b": float(np.mean([pb[t] for t in tasks])),
        "delta": float(d.mean()),
        "ci_low": float(lo),
        "ci_high": float(hi),
        "p_perm": p,
    }


def stratified_psr(df: pd.DataFrame, by: Sequence[str], task_col: str = "task_id", y_col: str = "survives", n_boot: int = 10000, seed: int = 12345) -> pd.DataFrame:
    rows = []
    for key, g in df.groupby(list(by), dropna=False):
        key = key if isinstance(key, tuple) else (key,)
        est = fast_cluster_bootstrap_psr(g, task_col, y_col, n_boot, seed)
        rows.append({**dict(zip(by, key)), "n_tasks": est.n_tasks, "n_variants": est.n_variants, "psr_task": est.point, "ci_low": est.ci_low, "ci_high": est.ci_high, "psr_variant": variant_level_psr(g, y_col)})
    return pd.DataFrame(rows)
