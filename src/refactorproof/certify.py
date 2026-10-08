"""Equivalence certification of candidate variants in a *separate* Lean file (Invariants C-E).

For each variant we emit ``artifacts/certificates/<task_id>/<variant_id>.lean``::

    <verbatim task prefix: imports, aux blocks, precondition definition>
    namespace RPOrig
      <original code_aux>  def f ... := <original body>
    end RPOrig
    namespace RPRef
      <transformed code_aux>  def f ... := <transformed body>
    end RPRef
    theorem rp_equiv_rfl       <binders> : RPOrig.f xs = RPRef.f xs := rfl
    theorem rp_equiv_simp_only <binders> : RPOrig.f xs = RPRef.f xs := by simp only [...]
    theorem rp_equiv_simp      <binders> : RPOrig.f xs = RPRef.f xs := by simp [...]

Lean elaborates every declaration independently, so one compile yields the
outcome of the whole certificate ladder; we attribute errors to declarations by
line range.  A variant is *certified* iff at least one ladder theorem elaborates
without error and the file contains no ``sorry``/``admit``.  The certificate file
is never imported by any survival file.

Usage::

    python -m refactorproof.certify --verina-root external/verina --variants artifacts/variants --workers 8
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .lean_runner import LeanRunner, LeanResult, contains_hole
from .transformations.base import Variant
from .transformations.helper_extract import parse_header
from .verina_parser import Block, TaskBlocks, add_def_modifier, load_task

LADDER = ("rfl", "rfl_nosmart", "delta_rfl", "simp_only", "simp")
RFL_LEVELS = ("rfl", "rfl_nosmart", "delta_rfl")  # definitional (kernel defeq) certificates
MAX_HEARTBEATS = 400000


def header_parts(tb: TaskBlocks) -> Tuple[str, str, str]:
    """Return (binders_text, applied_args, return_type) from the def header."""
    header = tb.def_header().strip()
    parsed = parse_header(header)
    m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*def\s+[^\s(:{\[]+\s*(?P<rest>.*):=$", header)
    if not m:
        raise ValueError(f"{tb.task_id}: cannot parse def header: {header!r}")
    rest = m.group("rest").strip()
    # split binders from return type at the top-level ' : '
    depth = 0
    split_at = None
    for i, ch in enumerate(rest):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            split_at = i
            break
    if split_at is None:
        raise ValueError(f"{tb.task_id}: no return type in header {header!r}")
    binders_text = rest[:split_at].strip()
    ret_type = rest[split_at + 1 :].strip()
    if parsed is None:
        raise ValueError(f"{tb.task_id}: header has non-explicit binders: {header!r}")
    _, names, _, _ = parsed
    return binders_text, " ".join(names), ret_type


def prefix_before(tb: TaskBlocks, key: str) -> str:
    out = []
    for s in tb.segments:
        if isinstance(s, Block):
            if s.key == key:
                break
            out.append(s.render())
        else:
            out.append(s)
    return "".join(out)


def build_certificate_source(tb: TaskBlocks, v: Variant) -> Tuple[str, Dict[str, Tuple[int, int]], Dict[str, Tuple[int, int]]]:
    fname = tb.signature.name
    binders_text, args, _ = header_parts(tb)
    header = tb.def_header()
    if not header.endswith("\n"):
        header += "\n"
    mod = (v.metadata or {}).get("header_modifier")
    ref_header = add_def_modifier(header, mod) if mod else header
    prefix = prefix_before(tb, "code_aux")
    if not prefix.endswith("\n"):
        prefix += "\n"

    def ns(name: str, aux: str, code: str, hdr: str) -> str:
        aux = aux if aux.endswith("\n") or not aux else aux + "\n"
        code = code if code.endswith("\n") else code + "\n"
        return f"namespace {name}\n{aux}\n{hdr}{code}end {name}\n"

    defs = [f"RPOrig.{fname}", f"RPRef.{fname}"] + [f"RPRef.{h}" for h in v.helper_names]
    defs_list = ", ".join(defs)
    law_sets = (v.metadata or {}).get("law_sets") or ([list(v.certificate_laws)] if v.certificate_laws else [[]])

    orig_aux = tb.content("code_aux")
    if v.transformed_code_aux.startswith(orig_aux):
        added_aux = v.transformed_code_aux[len(orig_aux):]
        shared_aux = orig_aux
    elif v.transformed_code_aux.startswith(orig_aux.rstrip("\n")):
        added_aux = v.transformed_code_aux[len(orig_aux.rstrip("\n")):]
        shared_aux = orig_aux
    else:  # transformation rewrote existing helpers: keep original in RPOrig, transformed in RPRef
        added_aux = v.transformed_code_aux
        shared_aux = ""
    # auxiliary constants introduced by `let rec` inside the bodies (namespace-distinct copies);
    # nested `let rec`s are named by their nesting path (f.outer.inner), inferred from indentation
    rec_names_orig = let_rec_constant_suffixes(tb.content("code"))
    rec_names_ref = let_rec_constant_suffixes(v.transformed_code)
    rec_names_added = let_rec_constant_suffixes(added_aux)
    delta_consts = list(defs)
    delta_consts += [f"RPOrig.{fname}.{r}" for r in rec_names_orig] + [f"RPRef.{fname}.{r}" for r in rec_names_ref]
    if v.helper_names:
        delta_consts += [f"RPRef.{v.helper_names[0]}.{r}" for r in rec_names_added]
    # After the outer rewrite is discharged, residual goals are typically `RPOrig.f.aux xs = RPRef.f.aux xs`
    # for textually identical `let rec` helpers; these are definitional once smart unfolding is off.
    # NB: `first` runs its LAST alternative with error recovery enabled, so an unknown constant in
    # `delta` must not be last; the smart-unfolding-off rfl is the most robust closer and goes last.
    unary = [c + "._unary" for c in delta_consts if "." in c[len("RPOrig."):] or "." in c[len("RPRef."):]]  # WF-compiled aux loops
    closer = (f"(first | rfl | (delta {' '.join(delta_consts)}; rfl)"
              + (f" | (delta {' '.join(delta_consts + unary)}; rfl)" if unary else "")
              + " | (set_option smartUnfolding false in rfl))")

    def simp_call(kind: str) -> str:
        """`simp`/`simp only` over defs + laws; several law sets are tried with `first` so that a
        lemma name missing from the task's environment does not sink the whole certificate."""
        alts = []
        seen = set()
        for laws in law_sets + ([[]] if len(law_sets) > 1 else []):
            key = tuple(laws)
            if key in seen:
                continue
            seen.add(key)
            alts.append(f"({kind} [{', '.join(defs + list(laws))}]) <;> {closer}")
        if len(alts) == 1:
            return "  " + alts[0]
        return "  first\n" + "\n".join(f"    | {a}" for a in alts)
    lhs, rhs = f"RPOrig.{fname} {args}", f"RPRef.{fname} {args}"
    stmt = f"{binders_text} :\n    {lhs} = {rhs}"

    parts: List[str] = []
    regions: Dict[str, Tuple[int, int]] = {}
    theorems: Dict[str, Tuple[int, int]] = {}

    def add(text: str, tag: Optional[str] = None, is_theorem: bool = False):
        start = sum(t.count("\n") for t in parts) + 1
        parts.append(text)
        end = sum(t.count("\n") for t in parts)
        if tag:
            (theorems if is_theorem else regions)[tag] = (start, end)

    # The UNCHANGED implementation helpers (original code_aux) are shared by both namespaces so that
    # both definitions refer to the same constants; only helpers *added* by the transformation go
    # inside RPRef.  (Duplicating code_aux would make e.g. RPOrig.sortList and RPRef.sortList
    # distinct recursive constants that no tactic can identify.)
    add(prefix, "prefix")
    if shared_aux.strip():
        add("\n-- shared (unchanged) implementation helpers\n" + shared_aux + ("\n" if not shared_aux.endswith("\n") else ""), "shared_aux")
    add("\n" + ns("RPOrig", "" if shared_aux else orig_aux, tb.content("code"), header), "orig")
    add("\n" + ns("RPRef", added_aux, v.transformed_code, ref_header), "ref")
    add(f"\nset_option maxHeartbeats {MAX_HEARTBEATS}\n")
    add(f"\ntheorem rp_equiv_rfl {stmt} := rfl\n", "rfl", True)
    # smart unfolding blocks rfl from unfolding structurally recursive functions applied to variables
    add(f"\nset_option smartUnfolding false in\ntheorem rp_equiv_rfl_nosmart {stmt} := rfl\n", "rfl_nosmart", True)
    add(f"\ntheorem rp_equiv_delta_rfl {stmt} := by\n  first\n    | (delta {' '.join(delta_consts)}; rfl)\n    | (delta {' '.join(delta_consts + unary)}; rfl)\n    | (set_option smartUnfolding false in rfl)\n", "delta_rfl", True)
    add(f"\ntheorem rp_equiv_simp_only {stmt} := by\n{simp_call('simp only')}\n", "simp_only", True)
    add(f"\ntheorem rp_equiv_simp {stmt} := by\n{simp_call('simp')}\n", "simp", True)
    for name, script in (v.extra_levels or []):
        body = script.replace("{DEFS}", defs_list).replace("{CLOSER}", closer)
        add(f"\ntheorem rp_equiv_{name} {stmt} := by\n  {body}\n", name, True)
    src = "".join(parts)
    if contains_hole(src):
        # Only possible if the task itself carries a hole in its prefix/code; refuse to certify.
        raise ValueError(f"{v.variant_id}: certificate source contains sorry/admit")
    return src, regions, theorems


def let_rec_constant_suffixes(code: str) -> List[str]:
    """Dotted suffixes of the auxiliary constants Lean creates for `let rec` bindings in ``code``
    (``outer``, ``outer.inner`` ...), using indentation to recover nesting."""
    stack: List[Tuple[int, str]] = []
    out: List[str] = []
    for line in code.splitlines():
        m = re.match(r"^(\s*)(?:.*?\b)?let\s+rec\s+([A-Za-z_][\w']*)", line)
        if not m:
            continue
        ind = len(m.group(1))
        while stack and stack[-1][0] >= ind:
            stack.pop()
        name = ".".join([n for _, n in stack] + [m.group(2)])
        out.append(name)
        stack.append((ind, m.group(2)))
    return out


def _in(line: int, rng: Tuple[int, int]) -> bool:
    return rng[0] <= line <= rng[1]


def judge(res: LeanResult, regions: Dict[str, Tuple[int, int]], theorems: Dict[str, Tuple[int, int]]) -> dict:
    errs = res.errors
    per = {}
    for name, rng in theorems.items():
        mine = [e for e in errs if _in(e.line, rng)]
        per[name] = {"ok": not mine and not res.timed_out, "errors": [e.text[:500] for e in mine]}
    region_errors = {name: [e.text[:500] for e in errs if _in(e.line, rng)] for name, rng in regions.items()}
    unattributed = [e for e in errs if not any(_in(e.line, r) for r in list(regions.values()) + list(theorems.values()))]
    build_error = None
    if region_errors.get("ref"):
        build_error = "variant_does_not_elaborate"
    elif region_errors.get("orig"):
        build_error = "original_does_not_elaborate"
    elif region_errors.get("prefix") or region_errors.get("shared_aux"):
        build_error = "prefix_does_not_elaborate"
    elif unattributed and not any(p["ok"] for p in per.values()):
        build_error = "unattributed_error"
    order = [n for n in LADDER if n in theorems] + [n for n in theorems if n not in LADDER]
    valid = build_error is None and any(per[n]["ok"] for n in order) and not res.timed_out
    level = next((n for n in order if per[n]["ok"]), None) if valid else None
    if res.timed_out:
        cat = "timeout_or_heartbeat"
    elif build_error:
        cat = build_error
    elif not valid:
        # attribute to the strongest ladder level that was attempted (simp), not the rfl attempt's "type mismatch"
        cat = None
        for name in reversed(order):
            mine = [e for e in errs if _in(e.line, theorems[name])]
            if mine:
                cat = mine[0].category
                break
        cat = cat or res.primary_category() or "other"
    else:
        cat = None
    codegen_hint = any("consider marking it as 'noncomputable'" in e for e in region_errors.get("ref", []))
    rfl_level = next((n for n in RFL_LEVELS if n in per and per[n]["ok"]), None) if valid else None
    return {
        "codegen_failure_hint": codegen_hint,
        "certificate_valid": valid,
        "certificate_closed_by_rfl": rfl_level is not None,   # definitional certificate at any rfl-class level
        "certificate_closed_by_plain_rfl": bool(per["rfl"]["ok"]) and build_error is None,
        "rfl_level": rfl_level,
        "certificate_level": level,
        "certificate_failure_category": cat,
        "per_theorem": per,
        "region_errors": {k: v for k, v in region_errors.items() if v},
        "unattributed_errors": [e.text[:300] for e in unattributed],
    }


def _compile_and_judge(runner, tb, v, cert_dir):
    src, regions, theorems = build_certificate_source(tb, v)
    lean_path = cert_dir / v.task_id / f"{v.variant_id}.lean"
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    lean_path.write_text(src, encoding="utf-8")
    res = runner.compile(lean_path)
    res.save(cert_dir / v.task_id / f"{v.variant_id}.compile.json")
    return lean_path, res, judge(res, regions, theorems)


def rejudge_variant(verina_root: Path, vdir: Path, cert_dir: Path) -> Optional[dict]:
    """Recompute certificate.json from the saved compile output (no Lean)."""
    payload = json.loads((vdir / "variant.json").read_text())
    v = Variant(**{k: payload.get(k, [] if k == "extra_levels" else None) for k in Variant.__dataclass_fields__ if k in payload or k == "extra_levels"})
    cj = cert_dir / v.task_id / f"{v.variant_id}.compile.json"
    out_json = vdir / "certificate.json"
    if not cj.exists() or not out_json.exists():
        return None
    from .lean_runner import LeanMessage

    d = json.loads(cj.read_text())
    res = LeanResult(command=d["command"], cwd=d["cwd"], file=d["file"], exit_code=d["exit_code"], stdout=d["stdout"], stderr=d["stderr"], elapsed_seconds=d["elapsed_seconds"], timed_out=d["timed_out"], messages=[LeanMessage(**m) for m in d["messages"]])
    tb = load_task(verina_root / "datasets" / "verina" / v.task_id)
    _, regions, theorems = build_certificate_source(tb, v)
    rec = json.loads(out_json.read_text())
    rec.update(judge(res, regions, theorems))
    out_json.write_text(json.dumps(rec, indent=1, ensure_ascii=False))
    return rec


def certify_variant(runner: LeanRunner, verina_root: Path, vdir: Path, cert_dir: Path, force: bool = False, retry_codegen: bool = True) -> dict:
    payload = json.loads((vdir / "variant.json").read_text())
    v = Variant(**{k: payload.get(k, [] if k == "extra_levels" else None) for k in Variant.__dataclass_fields__ if k in payload or k == "extra_levels"})
    out_json = vdir / "certificate.json"
    if out_json.exists() and not force:
        return json.loads(out_json.read_text())
    tb = load_task(verina_root / "datasets" / "verina" / v.task_id)
    lean_path, res, verdict = _compile_and_judge(runner, tb, v, cert_dir)
    retried = False
    if retry_codegen and not verdict["certificate_valid"] and verdict.get("codegen_failure_hint") and not (v.metadata or {}).get("header_modifier"):
        # Lean 4.18's code generator cannot compile some wrapped bodies ("depends on Bool.and.match_1");
        # the definition is logically fine, so mark it noncomputable (name/signature unchanged) and retry once.
        v.metadata = dict(v.metadata or {})
        v.metadata["header_modifier"] = "noncomputable"
        payload["metadata"] = v.metadata
        (vdir / "variant.json").write_text(json.dumps(payload, indent=1, ensure_ascii=False))
        lean_path, res, verdict = _compile_and_judge(runner, tb, v, cert_dir)
        retried = True
    rec = {
        "header_modifier": (v.metadata or {}).get("header_modifier"),
        "retried_noncomputable": retried,
        "task_id": v.task_id,
        "variant_id": v.variant_id,
        "transformation": v.transformation,
        "severity": v.severity,
        "equivalence_class": v.equivalence_class,
        "certificate_attempted": True,
        "certificate_file": str(lean_path),
        "lean_exit_code": res.exit_code,
        "lean_elapsed_seconds": res.elapsed_seconds,
        "timed_out": res.timed_out,
        **verdict,
    }
    out_json.write_text(json.dumps(rec, indent=1, ensure_ascii=False))
    return rec


def iter_variant_dirs(variants_root: Path, tasks: Optional[set] = None) -> List[Path]:
    out = []
    for vj in sorted(variants_root.glob("*/*/variant.json")):
        if tasks is None or vj.parent.parent.name in tasks:
            out.append(vj.parent)
    return out


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verina-root", type=Path, required=True)
    ap.add_argument("--variants", type=Path, default=Path("artifacts/variants"))
    ap.add_argument("--certificates", type=Path, default=Path("artifacts/certificates"))
    ap.add_argument("--results-dir", type=Path, default=Path("results"))
    ap.add_argument("--tasks", type=Path, help="restrict to task ids listed in this file")
    ap.add_argument("--only", nargs="*", help="restrict to these variant ids")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--force", action="store_true", help="recompile even if certificate.json exists")
    ap.add_argument("--rejudge", action="store_true", help="recompute verdicts from saved compile output, no Lean")
    ap.add_argument("--retry-codegen", action="store_true", help="re-certify variants whose certificate failed only because Lean could not generate code (adds `noncomputable`)")
    args = ap.parse_args(argv)

    tasks = None
    if args.tasks:
        tasks = {ln.strip() for ln in args.tasks.read_text().splitlines() if ln.strip()}
    vdirs = iter_variant_dirs(args.variants, tasks)
    if args.only:
        vdirs = [d for d in vdirs if d.name in set(args.only)]
    runner = LeanRunner(args.verina_root, timeout=args.timeout)
    if args.rejudge:
        n = 0
        for d in vdirs:
            if rejudge_variant(args.verina_root, d, args.certificates) is not None:
                n += 1
        print(f"[certify] rejudged {n} certificates", file=sys.stderr)
    force = args.force
    if args.retry_codegen:
        keep = []
        for d in vdirs:
            cj = d / "certificate.json"
            if cj.exists():
                c = json.loads(cj.read_text())
                if not c.get("certificate_valid") and c.get("codegen_failure_hint") and not c.get("header_modifier"):
                    keep.append(d)
        vdirs = keep
        force = True
        print(f"[certify] retrying {len(vdirs)} variants with codegen failures", file=sys.stderr)
    print(f"[certify] {len(vdirs)} variants, {args.workers} workers", file=sys.stderr)

    records = []
    with ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(certify_variant, runner, args.verina_root, d, args.certificates, force): d for d in vdirs}
        for i, f in enumerate(as_completed(futs), 1):
            d = futs[f]
            try:
                rec = f.result()
            except Exception as e:  # keep going; log the failure as a record
                rec = {"task_id": d.parent.name, "variant_id": d.name, "certificate_attempted": False, "certificate_valid": False, "certificate_closed_by_rfl": False, "certificate_failure_category": f"builder_error:{type(e).__name__}", "error": str(e)[:500]}
                (d / "certificate.json").write_text(json.dumps(rec, indent=1))
            records.append(rec)
            print(f"[certify] {i}/{len(vdirs)} {rec['variant_id']}: valid={rec.get('certificate_valid')} rfl={rec.get('certificate_closed_by_rfl')} level={rec.get('certificate_level')} cat={rec.get('certificate_failure_category')} {rec.get('lean_elapsed_seconds')}s", file=sys.stderr)

    # rewrite the aggregate from all certificate.json files present (so partial runs merge)
    args.results_dir.mkdir(parents=True, exist_ok=True)
    all_recs = []
    for cj in sorted(args.variants.glob("*/*/certificate.json")):
        all_recs.append(json.loads(cj.read_text()))
    with (args.results_dir / "certification.jsonl").open("w") as f:
        for r in all_recs:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    n_valid = sum(1 for r in all_recs if r.get("certificate_valid"))
    n_rfl = sum(1 for r in all_recs if r.get("certificate_closed_by_rfl"))
    print(f"[certify] total certificates={len(all_recs)} valid={n_valid} rfl={n_rfl}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
