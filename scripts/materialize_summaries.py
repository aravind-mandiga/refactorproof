#!/usr/bin/env python3
"""Rebuild artifacts/model_proofs/<model>/<task>/summary.json from results/model_proofs.jsonl.

The per-task generation summaries are how `revision_v2` reads the K samples of each task.  The released
archive ships the one canonical record of every sample (results/model_proofs.jsonl) rather than the
generation directories, whose bulk is raw model responses; this script expands it back:

    python scripts/materialize_summaries.py

Every field the analysis reads (attempt index, Lean validity, proof text, hashes) is carried over
unchanged.  The raw model response of each sample is not part of the release.
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--proofs", type=Path, default=Path("results/model_proofs.jsonl"))
    ap.add_argument("--out", type=Path, default=Path("artifacts/model_proofs"))
    args = ap.parse_args(argv)

    by_task = collections.defaultdict(list)
    with args.proofs.open(encoding="utf-8") as fh:
        for line in fh:
            rec = json.loads(line)
            by_task[(rec["model_id"], rec["task_id"])].append(rec)

    for (model_id, task_id), attempts in sorted(by_task.items()):
        attempts.sort(key=lambda a: int(a["attempt"]))
        primary = next((int(a["attempt"]) for a in attempts if a.get("is_primary") in (True, "True")), None)
        summary = {
            "task_id": task_id,
            "model_id": model_id,
            "n_attempts": len(attempts),
            "n_valid": sum(1 for a in attempts if a.get("original_proof_valid") in (True, "True")),
            "primary_attempt": primary,
            "attempts": attempts,
        }
        d = args.out / model_id / task_id
        d.mkdir(parents=True, exist_ok=True)
        (d / "summary.json").write_text(json.dumps(summary, indent=1), encoding="utf-8")

    models = sorted({m for m, _ in by_task})
    print(f"[materialize] {len(by_task)} summaries for {len(models)} generation runs under {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
