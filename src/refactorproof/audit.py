"""Audit all VERINA tasks: parse, detect usable reference proofs, compile originals.

Usage::

    python -m refactorproof.audit --verina-root external/verina [--workers 8] [--no-compile]

Writes ``data/verina_audit.csv``, ``data/all_tasks.txt``, ``data/reference_tasks.txt``,
``data/environment.json`` and per-task compile logs under ``artifacts/original_compiles/``.
Stops with a non-zero exit if the usable reference-proof count is not 46.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional

from .lean_runner import LeanRunner
from .verina_parser import iter_task_dirs, load_task, tier_of

AUDIT_FIELDS = [
    "task_id",
    "tier",
    "function_name",
    "n_parameters",
    "parameters",
    "return_type",
    "proof_block_nonempty",
    "contains_sorry_in_proof",
    "has_reference_proof_text",
    "original_compiles",
    "original_compile_seconds",
    "original_error_category",
    "has_reference_proof",
    "code_loc",
    "code_aux_loc",
    "proof_loc",
    "proof_aux_loc",
    "precond_is_true",
    "spec_hash",
    "proof_hash",
    "code_has_termination_by",
    "code_has_where",
    "code_has_do",
    "code_has_let_rec",
    "code_first_token",
    "task_has_upstream_axioms",
]


def audit_task(task_dir: Path) -> Dict:
    tb = load_task(task_dir)
    code = tb.content("code")
    proof = tb.block("proof")
    import re

    first = code.strip().split()[0] if code.strip() else ""
    row = {
        "task_id": tb.task_id,
        "tier": tier_of(tb.task_id),
        "function_name": tb.signature.name,
        "n_parameters": len(tb.signature.parameters),
        "parameters": json.dumps(tb.signature.parameters, ensure_ascii=False),
        "return_type": tb.signature.return_type,
        "proof_block_nonempty": proof.stripped() != "",
        "contains_sorry_in_proof": proof.has_hole(),
        "has_reference_proof_text": tb.has_reference_proof_text(),
        "original_compiles": None,
        "original_compile_seconds": None,
        "original_error_category": None,
        "has_reference_proof": None,
        "code_loc": tb.loc("code"),
        "code_aux_loc": tb.loc("code_aux"),
        "proof_loc": tb.loc("proof"),
        "proof_aux_loc": tb.loc("proof_aux"),
        "precond_is_true": tb.content("precond").strip() == "True",
        "spec_hash": tb.spec_hash(),
        "proof_hash": tb.proof_hash(),
        "code_has_termination_by": bool(re.search(r"\btermination_by\b", code)),
        "code_has_where": bool(re.search(r"^\s*where\b", code, re.M)),
        "code_has_do": bool(re.search(r"\bdo\b", code)),
        "code_has_let_rec": bool(re.search(r"\blet\s+rec\b", code)),
        "code_first_token": first,
        "task_has_upstream_axioms": bool(re.search(r"^\s*axiom\s", tb.render(), re.M)),
    }
    return row


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, default=Path("data"))
    ap.add_argument("--log-dir", type=Path, default=Path("artifacts/original_compiles"))
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--no-compile", action="store_true", help="skip Lean compilation of originals")
    ap.add_argument("--expected-reference", type=int, default=46)
    ap.add_argument("--only", nargs="*", help="restrict to these task ids (debugging)")
    args = ap.parse_args(argv)

    task_dirs = iter_task_dirs(args.verina_root)
    if args.only:
        task_dirs = [d for d in task_dirs if d.name in set(args.only)]
    print(f"[audit] {len(task_dirs)} task directories", file=sys.stderr)

    rows = [audit_task(d) for d in task_dirs]

    if not args.no_compile:
        runner = LeanRunner(args.verina_root, timeout=args.timeout)
        env_info = runner.version_info()
        args.log_dir.mkdir(parents=True, exist_ok=True)
        by_id = {r["task_id"]: r for r in rows}

        def job(d: Path):
            res = runner.compile(d / "task.lean")
            res.save(args.log_dir / f"{d.name}.json")
            return d.name, res

        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            futs = [ex.submit(job, d) for d in task_dirs]
            for i, f in enumerate(as_completed(futs), 1):
                tid, res = f.result()
                r = by_id[tid]
                r["original_compiles"] = res.ok
                r["original_compile_seconds"] = res.elapsed_seconds
                r["original_error_category"] = res.primary_category()
                print(f"[audit] {i}/{len(task_dirs)} {tid}: ok={res.ok} {res.elapsed_seconds}s", file=sys.stderr)
    else:
        env_info = {"note": "compilation skipped"}

    for r in rows:
        r["has_reference_proof"] = bool(r["has_reference_proof_text"] and (r["original_compiles"] is None or r["original_compiles"]))

    args.out_dir.mkdir(parents=True, exist_ok=True)
    with (args.out_dir / "verina_audit.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=AUDIT_FIELDS)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    (args.out_dir / "all_tasks.txt").write_text("".join(r["task_id"] + "\n" for r in rows))
    ref = [r["task_id"] for r in rows if r["has_reference_proof"]]
    (args.out_dir / "reference_tasks.txt").write_text("".join(t + "\n" for t in ref))
    (args.out_dir / "environment.json").write_text(json.dumps(env_info, indent=1))

    n_compiled = sum(1 for r in rows if r["original_compiles"])
    n_text_ref = sum(1 for r in rows if r["has_reference_proof_text"])
    print(
        f"[audit] tasks={len(rows)} text_reference_proofs={n_text_ref} usable_reference_proofs={len(ref)} "
        f"originals_compiled={n_compiled if not args.no_compile else 'skipped'}",
        file=sys.stderr,
    )
    if not args.only and len(ref) != args.expected_reference:
        print(f"[audit] ERROR: expected {args.expected_reference} usable reference proofs, found {len(ref)}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
