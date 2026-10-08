"""Import proofs from a VERINA benchmark output directory (rounds_report_*.json) into results/model_proofs.jsonl.

Use this only when proofs were generated with VERINA's own `scripts/benchmark.py` (e.g. API models run
elsewhere) instead of `refactorproof.gen_proofs`.  Each round r of a task becomes attempt r; every
imported proof is re-checked with Lean on the original task file so the "first Lean-valid" selection rule
is applied identically to all models.

    python -m refactorproof.import_model_proofs --verina-root external/verina --verina-output <dir> --model-id gpt-4.1
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import List, Optional

from .gen_proofs import lean_check
from .lean_runner import LeanRunner


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--verina-output", type=Path, required=True)
    ap.add_argument("--model-id", required=True)
    ap.add_argument("--task-name", default="execute_proof_gen")
    ap.add_argument("--out", type=Path, default=Path("artifacts/model_proofs"))
    ap.add_argument("--results-dir", type=Path, default=Path("results"))
    ap.add_argument("--workers", type=int, default=8)
    args = ap.parse_args(argv)

    reports = sorted(args.verina_output.glob("rounds_report_*.json"), key=lambda p: p.stem.split("_")[-1])
    if not reports:
        print("no rounds_report_*.json found", file=sys.stderr)
        return 1
    rep = json.loads(reports[-1].read_text())
    runner = LeanRunner(args.verina_root)
    jobs = []
    for r_idx, round_rep in sorted(rep["rounds"].items(), key=lambda kv: int(kv[0])):
        for task_id, dr in round_rep["data_reports"].items():
            tr = dr["task_reports"].get(args.task_name)
            if not tr:
                continue
            art = tr["artifact"]
            rec = {"attempt": int(r_idx), "imports": art.get("imports", ""), "proof_aux": art.get("proof_aux", ""), "proof": art.get("proof", ""), "format_ok": bool(art.get("proof", "").strip()) and art.get("proof", "").strip() != "sorry", "raw_response": None, "verina_scores": tr.get("scores", {})}
            jobs.append((task_id, rec))
    by_task = {}
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = []
        for task_id, rec in jobs:
            tdir = args.out / args.model_id / task_id
            tdir.mkdir(parents=True, exist_ok=True)
            futs.append((task_id, ex.submit(lean_check, runner, args.verina_root, task_id, rec, tdir)))
        for task_id, f in futs:
            by_task.setdefault(task_id, []).append(f.result())
    rows = {}
    mp = args.results_dir / "model_proofs.jsonl"
    if mp.exists():
        for ln in mp.read_text().splitlines():
            if ln.strip():
                d = json.loads(ln)
                rows[f"{d['model_id']}|{d['task_id']}|{d['attempt']}"] = d
    n_cov = 0
    for task_id, recs in by_task.items():
        recs.sort(key=lambda r: r["attempt"])
        primary = next((r["attempt"] for r in recs if r.get("original_proof_valid")), None)
        n_cov += primary is not None
        for r in recs:
            r.update({"model_id": args.model_id, "task_id": task_id, "is_primary": r["attempt"] == primary, "source": str(args.verina_output), "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S")})
            rows[f"{args.model_id}|{task_id}|{r['attempt']}"] = {k: v for k, v in r.items() if k != "raw_response"}
    with mp.open("w") as f:
        for k in sorted(rows):
            f.write(json.dumps(rows[k], ensure_ascii=False) + "\n")
    print(f"[import_model_proofs] {args.model_id}: tasks={len(by_task)} with_valid_proof={n_cov}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
