"""LLM proof generation on the ORIGINAL implementations (Phase 5), via VERINA's prompting code.

Protocol (frozen in configs/models.yaml):
  * for each task, draw K independent samples in a fixed order (attempt 0..K-1) on the original code;
  * every sample is Lean-checked on the original task file (proof/proof_aux/imports blocks replaced);
  * the first Lean-valid attempt is the *primary* proof for survival analysis; all attempts are logged;
  * no proof is ever generated or repaired after seeing a refactored implementation.

Must run inside the VERINA Python environment with ``PYTHONPATH=src:external/verina/src``::

    python -m refactorproof.gen_proofs --verina-root external/verina --models-config configs/models.yaml \
        --model qwen3-14b --api-base http://127.0.0.1:8000/v1/ --tasks data/all_tasks.txt --lean-workers 16

Outputs
  artifacts/model_proofs/<model_id>/<task_id>/attempt_<k>.json   raw response, parsed blocks, Lean result
  artifacts/model_proofs/<model_id>/<task_id>/attempt_<k>.lean   the original task with the model proof
  results/model_proofs.jsonl                                       one row per attempt (merged across models)
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Dict, List, Optional

import yaml

from .lean_runner import LeanRunner, contains_hole
from .survival import ProofArtifact, apply_proof, block_line_range
from .verina_parser import load_task

CHEAT_RE_WORDS = ("sorry", "admit", "axiom")


def _verina_imports(verina_root: Path):
    sys.path.insert(0, str(verina_root / "src"))
    import dspy  # noqa
    from dotenv import load_dotenv

    load_dotenv(verina_root / ".env", override=False)
    from verina.baseline.custom_prompt_proof import CustomPromptHandler, parse_model_response, prepare_prompt
    from verina.baseline.generate import dspy_generate_proof
    from verina.benchmark.evaluation_tasks import benchmark_data_to_gen_proof_fewshot_example, benchmark_data_to_gen_proof_input
    from verina.dataset.dataset import load_benchmark_data_from_task_file
    from verina.utils.lm import LMConfig

    return dict(
        dspy=dspy,
        CustomPromptHandler=CustomPromptHandler,
        parse_model_response=parse_model_response,
        prepare_prompt=prepare_prompt,
        dspy_generate_proof=dspy_generate_proof,
        to_input=benchmark_data_to_gen_proof_input,
        to_fewshot=benchmark_data_to_gen_proof_fewshot_example,
        load_bd=load_benchmark_data_from_task_file,
        LMConfig=LMConfig,
    )


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def dedent_block(block: str) -> str:
    """Remove the common indentation of all non-blank lines (top-level declarations, e.g. proof_aux)."""
    lines = block.rstrip("\n").splitlines()
    nb = [l for l in lines if l.strip()]
    if not nb:
        return ""
    common = min(_indent(l) for l in nb)
    return "".join((l[common:] if l.strip() else "") + "\n" for l in lines)


def normalize_proof_block(block: str) -> str:
    """Re-indent a model proof so every top-level tactic sits at two spaces.

    Field parsers (dspy, our code-block extractor) strip the leading whitespace of the *first* line only,
    so a proof that came back as ``unfold f\n    simp_all`` would otherwise make ``simp_all`` a continuation
    of the ``unfold`` line ("unknown identifier 'simp_all'").  We align the first line with the common
    indentation of the remaining lines and then indent the whole block by two spaces, preserving relative
    indentation inside nested tactic blocks."""
    lines = block.strip("\n").splitlines()
    if not lines:
        return ""
    first_ind = _indent(lines[0])
    rest = [l for l in lines[1:] if l.strip()]
    if rest:
        rest_min = min(_indent(l) for l in rest)
    else:
        rest_min = first_ind
    if first_ind == 0 and rest_min > 0:
        body = [lines[0].strip()] + [(l[rest_min:] if l.strip() else "") for l in lines[1:]]
    else:
        common = min([first_ind] + ([rest_min] if rest else []))
        body = [(l[common:] if l.strip() else "") for l in lines]
    return "".join(("  " + l if l.strip() else "") + "\n" for l in body)


def has_cheat(text: str) -> bool:
    """True if sorry/admit/axiom occurs as a token outside comments (Lean additionally flags any real
    `sorry` with a warning, which lean_check also rejects)."""
    import re

    text = text or ""
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--.*?$", "", text, flags=re.M)
    return any(re.search(r"(?<![\w'.])" + w + r"(?![\w'])", text) for w in CHEAT_RE_WORDS)


PROOF_PLACEHOLDER = "{{`proof` WILL BE FILLED HERE}}"


async def sample_one(V, style: str, lm, handler, gp_input, fewshots, attempt: int, instruction: Optional[str] = None, forced_prefix: Optional[str] = None) -> Dict:
    """One sample.  ``instruction`` (Experiment B, strategy conditions) is appended to the prover prompt
    (custom_prompt) or prefixed to the task description (baseline); the task itself is unchanged."""
    t0 = time.time()
    rec: Dict = {"attempt": attempt, "started_at": t0}
    try:
        if style == "baseline":
            if instruction:
                gp_input = gp_input.model_copy(update={"description": instruction + "\n\n" + gp_input.description})
            out = await V["dspy_generate_proof"](V["dspy"].Predict, gp_input, fewshots)
            raw = getattr(lm, "history", [])
            rec["raw_response"] = raw[-1].get("outputs", [""])[0] if raw else ""
        elif style == "custom_prompt":
            messages = V["prepare_prompt"](handler, gp_input)
            if instruction or forced_prefix:
                messages = [dict(m) for m in messages]
            if forced_prefix:
                # hard intervention: the proof stub already starts with the forced first tactic
                messages[-1]["content"] = messages[-1]["content"].replace(PROOF_PLACEHOLDER, forced_prefix + "\n  " + PROOF_PLACEHOLDER, 1)
            if instruction:
                messages[-1]["content"] = messages[-1]["content"].rstrip() + "\n\n" + instruction
            resp = await lm.acall(messages=messages)
            text = resp[0] if isinstance(resp, list) else str(resp)
            rec["raw_response"] = text
            out = V["parse_model_response"](gp_input, text)
            if forced_prefix and (out.proof or "").strip() and (out.proof or "").strip() != "sorry":
                first = next((ln.strip() for ln in out.proof.splitlines() if ln.strip()), "")
                echoed = first.startswith(forced_prefix.strip())
                rec["forced_prefix"] = forced_prefix
                rec["forced_prefix_echoed"] = echoed
                if not echoed:  # enforce the intervention regardless of whether the model copied the stub line
                    body = out.proof.strip("\n")
                    ind = len(body) - len(body.lstrip(" ")) if body else 2
                    out = out.model_copy(update={"proof": " " * max(ind, 2) + forced_prefix + "\n" + body})
        else:
            raise ValueError(style)
        rec.update({"imports": out.imports or "", "proof_aux": out.proof_aux or "", "proof": out.proof or "", "format_ok": bool((out.proof or "").strip()) and (out.proof or "").strip() != "sorry"})
    except Exception as e:  # format / API failures are attempts too
        rec.update({"imports": "", "proof_aux": "", "proof": "", "format_ok": False, "error": f"{type(e).__name__}: {str(e)[:400]}"})
    rec["gen_seconds"] = round(time.time() - t0, 2)
    return rec


def lean_check(runner: LeanRunner, verina_root: Path, task_id: str, rec: Dict, out_dir: Path) -> Dict:
    tb = load_task(verina_root / "datasets" / "verina" / task_id)
    art = ProofArtifact("model", rec["proof"], rec["proof_aux"], extra_imports=rec.get("imports", ""))
    rec["has_cheat"] = has_cheat(rec["proof"]) or has_cheat(rec["proof_aux"])
    if not rec["format_ok"] or rec["has_cheat"]:
        rec.update({"original_proof_valid": False, "lean_checked": False, "invalid_reason": "format" if not rec["format_ok"] else "cheat_code"})
        return rec
    art.proof = normalize_proof_block(art.proof)
    art.proof_aux = dedent_block(art.proof_aux) if art.proof_aux.strip() else tb.content("proof_aux")
    tb_eval = apply_proof(tb, art)
    assert tb_eval.spec_hash() == tb.spec_hash()
    assert tb_eval.content("code") == tb.content("code") and tb_eval.content("code_aux") == tb.content("code_aux")
    lean_path = out_dir / f"attempt_{rec['attempt']}.lean"
    lean_path.write_text(tb_eval.render(), encoding="utf-8")
    res = runner.compile(lean_path)
    res.save(out_dir / f"attempt_{rec['attempt']}.compile.json")
    sorry_warn = any("sorry" in m.text for m in res.messages if m.severity == "warning")
    valid = res.ok and not sorry_warn
    rec.update(
        {
            "lean_checked": True,
            "original_proof_valid": bool(valid),
            "lean_exit_code": res.exit_code,
            "lean_elapsed_seconds": res.elapsed_seconds,
            "error_category": None if valid else res.primary_category(),
            "first_error": None if valid else (res.errors[0].text[:400] if res.errors else None),
            "proof_text": art.proof,
            "proof_aux_text": art.proof_aux,
            "imports_text": tb_eval.content("import"),
            "proof_hash": tb_eval.proof_hash(),
            "imports_hash": tb_eval.block("import").sha256(),
            "invalid_reason": None if valid else "lean_error",
        }
    )
    return rec


async def run(args) -> int:
    cfg = yaml.safe_load(Path(args.models_config).read_text())
    mcfg = cfg["models"][args.model]
    proto = cfg["protocol"]
    K = args.K or proto["K"]
    V = _verina_imports(args.verina_root)
    dspy = V["dspy"]
    api_base = args.api_base or mcfg.get("api_base")
    lm = V["LMConfig"](
        provider=mcfg["provider"],
        model_name=mcfg["served_model_name"],
        api_base=api_base,
        api_key=os.environ.get("RP_LOCAL_API_KEY", "EMPTY") if mcfg["provider"] == "local" else None,
        temperature=float(mcfg.get("temperature", 1.0)),
        max_tokens=int(mcfg.get("max_tokens", 10000)),
    ).get_model()
    # per-request timeout forwarded by dspy to litellm; long prover completions on large models need more
    # than the default (Goedel-32B at 32 concurrent requests hit litellm timeouts at ~3000 s)
    try:
        lm.kwargs["timeout"] = float(args.lm_timeout)
    except Exception as e:  # pragma: no cover
        print(f"[gen_proofs] could not set LM timeout: {e}", file=sys.stderr)
    dspy.configure(lm=lm)
    style = mcfg["prompt_style"]
    if mcfg.get("neutral_prompt") and style == "baseline":
        # remove VERINA's tactic hint ("Unfold the implementation and specification definitions when
        # necessary" / "Unfold the precondition definitions at h_precond when necessary") so the general-model
        # prompt carries no strategy nudge; everything else in the signature is unchanged
        from verina.baseline.generate import BaselineGenProofSig, GEN_PROOF_PROMPT
        neutral = "\n".join(ln for ln in GEN_PROOF_PROMPT.splitlines() if not ln.strip().startswith("- Unfold") and ln.strip() != "Hint:")
        BaselineGenProofSig.instructions = neutral
        print("[gen_proofs] neutral prompt: removed VERINA's unfold hint lines from the dspy instructions", file=sys.stderr)
    handler = V["CustomPromptHandler"](None) if style == "custom_prompt" else None

    wanted = None
    if args.tasks:
        wanted = [ln.strip() for ln in Path(args.tasks).read_text().splitlines() if ln.strip()]
    ds_dir = args.verina_root / "datasets" / "verina"
    task_ids = wanted or sorted(d.name for d in ds_dir.iterdir() if d.is_dir() and d.name.startswith("verina_"))
    if args.only:
        task_ids = [t for t in task_ids if t in set(args.only)]
    fewshot_names = proto.get("fewshot_example_names", [])
    fewshots = [V["to_fewshot"](V["load_bd"](ds_dir / n, ds_dir / n / "task.json")) for n in fewshot_names] if style == "baseline" else []

    out_root = args.out / args.model
    out_root.mkdir(parents=True, exist_ok=True)
    runner = LeanRunner(args.verina_root, timeout=proto.get("lean_timeout_seconds", 300))
    sem = asyncio.Semaphore(args.concurrency)
    pool = ThreadPoolExecutor(max_workers=args.lean_workers)
    loop = asyncio.get_running_loop()
    gen_params = {"temperature": mcfg.get("temperature", 1.0), "max_tokens": mcfg.get("max_tokens"), "K": K, "prompt_style": style, "served_model_name": mcfg["served_model_name"], "provider": mcfg["provider"], "api_base": api_base, "strategy_condition": mcfg.get("strategy_condition", "default"), "strategy_instruction": mcfg.get("strategy_instruction"), "concurrency": args.concurrency, "lm_timeout_s": args.lm_timeout, "neutral_prompt": bool(mcfg.get("neutral_prompt")), "forced_prefix": mcfg.get("forced_prefix")}

    async def do_task(task_id: str):
        tdir = out_root / task_id
        tdir.mkdir(parents=True, exist_ok=True)
        done_path = tdir / "summary.json"
        if done_path.exists() and not args.force:
            return json.loads(done_path.read_text())
        bd = V["load_bd"](ds_dir / task_id, ds_dir / task_id / "task.json")
        gp_input = V["to_input"](bd)
        instruction = None
        forced_prefix = None
        if mcfg.get("strategy_instruction") or mcfg.get("forced_prefix"):
            _tb = load_task(ds_dir / task_id)
            _f = _tb.signature.name if _tb.signature else (_tb.def_header_name() or "the implementation")
            if mcfg.get("strategy_instruction"):
                instruction = mcfg["strategy_instruction"].format(fname=_f, postcond=f"{_f}_postcond")
            if mcfg.get("forced_prefix"):
                forced_prefix = mcfg["forced_prefix"].format(fname=_f, postcond=f"{_f}_postcond")

        async def one(k):
            async with sem:
                rec_ = await sample_one(V, style, lm, handler, gp_input, fewshots, k, instruction, forced_prefix)
                if instruction:
                    rec_["strategy_instruction_filled"] = instruction  # exact text appended to this task's prompt
                return rec_

        recs = await asyncio.gather(*[one(k) for k in range(K)])
        checked = await asyncio.gather(*[loop.run_in_executor(pool, lean_check, runner, args.verina_root, task_id, r, tdir) for r in recs])
        primary = next((r["attempt"] for r in sorted(checked, key=lambda r: r["attempt"]) if r.get("original_proof_valid")), None)
        for r in checked:
            r.update({"model_id": args.model, "model_family": mcfg.get("family"), "base_model": mcfg.get("base_model", args.model), "strategy_condition": mcfg.get("strategy_condition", "default"), "task_id": task_id, "is_primary": r["attempt"] == primary, "is_fewshot_example": task_id in fewshot_names, "gen_params": gen_params, "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S")})
            (tdir / f"attempt_{r['attempt']}.json").write_text(json.dumps(r, indent=1, ensure_ascii=False))
        summary = {"task_id": task_id, "model_id": args.model, "n_attempts": K, "n_valid": sum(1 for r in checked if r.get("original_proof_valid")), "primary_attempt": primary, "attempts": sorted(checked, key=lambda r: r["attempt"])}
        done_path.write_text(json.dumps(summary, indent=1, ensure_ascii=False))
        print(f"[gen_proofs] {args.model} {task_id}: valid={summary['n_valid']}/{K} primary={primary}", file=sys.stderr)
        return summary

    task_sem = asyncio.Semaphore(args.task_concurrency)

    async def guarded(t):
        async with task_sem:
            try:
                return await do_task(t)
            except Exception as e:
                print(f"[gen_proofs] {t} FAILED: {type(e).__name__}: {e}", file=sys.stderr)
                return {"task_id": t, "model_id": args.model, "error": str(e)[:500], "attempts": []}

    summaries = await asyncio.gather(*[guarded(t) for t in task_ids])

    # merge into results/model_proofs.jsonl (all models)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    mp = args.results_dir / "model_proofs.jsonl"
    rows: Dict[str, dict] = {}
    if mp.exists():
        for ln in mp.read_text().splitlines():
            if ln.strip():
                d = json.loads(ln)
                rows[f"{d['model_id']}|{d['task_id']}|{d['attempt']}"] = d
    for s in summaries:
        for r in s.get("attempts", []):
            slim = {k: v for k, v in r.items() if k not in ("raw_response",)}
            rows[f"{r['model_id']}|{r['task_id']}|{r['attempt']}"] = slim
    with mp.open("w") as f:
        for k in sorted(rows):
            f.write(json.dumps(rows[k], ensure_ascii=False) + "\n")
    n_tasks = len(summaries)
    n_cov = sum(1 for s in summaries if s.get("primary_attempt") is not None)
    print(f"[gen_proofs] {args.model}: tasks={n_tasks} with_valid_proof={n_cov} coverage={n_cov/max(n_tasks,1):.3f}", file=sys.stderr)
    return 0


def recheck(args) -> int:
    """Re-validate every saved attempt of a model with the current normalisation and rebuild summaries
    and results/model_proofs.jsonl.  Raw generations are never modified."""
    cfg = yaml.safe_load(Path(args.models_config).read_text())
    proto = cfg["protocol"]
    mcfg = cfg["models"][args.model]
    out_root = args.out / args.model
    runner = LeanRunner(args.verina_root, timeout=proto.get("lean_timeout_seconds", 300))
    tdirs = sorted(d for d in out_root.iterdir() if d.is_dir() and (d / "summary.json").exists())
    if args.only:
        tdirs = [d for d in tdirs if d.name in set(args.only)]
    print(f"[recheck] {args.model}: {len(tdirs)} tasks, {args.lean_workers} workers", file=sys.stderr)
    fewshot_names = proto.get("fewshot_example_names", [])

    def do_task(tdir: Path):
        recs = []
        for aj in sorted(a for a in tdir.glob("attempt_*.json") if not a.name.endswith(".compile.json")):
            r = json.loads(aj.read_text())
            if r.get("attempt") is None:
                continue
            base = {k: r.get(k) for k in ("attempt", "started_at", "raw_response", "imports", "proof_aux", "proof", "format_ok", "error", "gen_seconds", "gen_params", "timestamp")}
            if not base.get("gen_params"):  # reconstruct from the frozen config if an earlier recheck dropped it
                base["gen_params"] = {"temperature": mcfg.get("temperature", 1.0), "max_tokens": mcfg.get("max_tokens"), "K": proto.get("K"), "prompt_style": mcfg.get("prompt_style"), "served_model_name": mcfg.get("served_model_name"), "provider": mcfg.get("provider"), "strategy_condition": mcfg.get("strategy_condition", "default"), "strategy_instruction": mcfg.get("strategy_instruction"), "reconstructed_from_config": True}
            for k in ("imports", "proof_aux", "proof"):
                base[k] = base.get(k) or ""
            base["format_ok"] = bool(base.get("format_ok")) and bool(base["proof"].strip())
            recs.append(lean_check(runner, args.verina_root, tdir.name, base, tdir))
        primary = next((r["attempt"] for r in sorted(recs, key=lambda r: r["attempt"]) if r.get("original_proof_valid")), None)
        for r in recs:
            r.update({"model_id": args.model, "model_family": mcfg.get("family"), "base_model": mcfg.get("base_model", args.model), "strategy_condition": mcfg.get("strategy_condition", "default"), "task_id": tdir.name, "is_primary": r["attempt"] == primary, "is_fewshot_example": tdir.name in fewshot_names, "rechecked_at": time.strftime("%Y-%m-%dT%H:%M:%S")})
            (tdir / f"attempt_{r['attempt']}.json").write_text(json.dumps(r, indent=1, ensure_ascii=False))
        summary = {"task_id": tdir.name, "model_id": args.model, "n_attempts": len(recs), "n_valid": sum(1 for r in recs if r.get("original_proof_valid")), "primary_attempt": primary, "attempts": sorted(recs, key=lambda r: r["attempt"])}
        (tdir / "summary.json").write_text(json.dumps(summary, indent=1, ensure_ascii=False))
        return summary

    summaries = []
    with ThreadPoolExecutor(max_workers=args.lean_workers) as ex:
        for i, s in enumerate(ex.map(do_task, tdirs), 1):
            summaries.append(s)
            print(f"[recheck] {i}/{len(tdirs)} {s['task_id']}: valid={s['n_valid']}/{s['n_attempts']} primary={s['primary_attempt']}", file=sys.stderr)
    _merge_model_proofs(args, summaries)
    n_cov = sum(1 for s in summaries if s.get("primary_attempt") is not None)
    print(f"[recheck] {args.model}: tasks={len(summaries)} with_valid_proof={n_cov} coverage={n_cov/max(len(summaries),1):.3f}", file=sys.stderr)
    return 0


def _merge_model_proofs(args, summaries) -> None:
    args.results_dir.mkdir(parents=True, exist_ok=True)
    mp = args.results_dir / "model_proofs.jsonl"
    rows: Dict[str, dict] = {}
    if mp.exists():
        for ln in mp.read_text().splitlines():
            if ln.strip():
                d = json.loads(ln)
                rows[f"{d['model_id']}|{d['task_id']}|{d['attempt']}"] = d
    for s in summaries:
        for r in s.get("attempts", []):
            slim = {k: v for k, v in r.items() if k not in ("raw_response",)}
            rows[f"{r['model_id']}|{r['task_id']}|{r['attempt']}"] = slim
    with mp.open("w") as f:
        for k in sorted(rows):
            f.write(json.dumps(rows[k], ensure_ascii=False) + "\n")


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--models-config", type=Path, default=Path("configs/models.yaml"))
    ap.add_argument("--model", required=True, help="key in configs/models.yaml")
    ap.add_argument("--api-base", help="override api_base (e.g. vLLM URL)")
    ap.add_argument("--tasks", type=Path)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--K", type=int)
    ap.add_argument("--out", type=Path, default=Path("artifacts/model_proofs"))
    ap.add_argument("--results-dir", type=Path, default=Path("results"))
    ap.add_argument("--concurrency", type=int, default=16, help="concurrent LM requests")
    ap.add_argument("--lm-timeout", type=float, default=7200.0, help="per-request LM timeout in seconds (litellm)")
    ap.add_argument("--task-concurrency", type=int, default=8)
    ap.add_argument("--lean-workers", type=int, default=8)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--recheck", action="store_true", help="re-run the Lean check on saved attempts (no generation)")
    args = ap.parse_args(argv)
    if args.recheck:
        return recheck(args)
    return asyncio.run(run(args))


if __name__ == "__main__":
    sys.exit(main())
