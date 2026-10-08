"""Deterministic text-level proof features for the mechanism analysis (RQ3).

Features are computed on the proof block (plus proof_aux) that is held fixed
across original and refactored evaluation.  ``target`` is the implementation
function name; ``aux_identifiers`` are identifiers defined in code_aux /
solution_aux (helpers the proof may depend on).
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass
from typing import Dict, Iterable, List, Optional

TACTICS = [
    "unfold", "simp", "simp_all", "simp?", "rw", "rwa", "have", "exact", "apply", "intro", "intros",
    "constructor", "cases", "rcases", "obtain", "induction", "split", "by_cases", "omega", "decide",
    "native_decide", "rfl", "aesop", "grind", "norm_num", "linarith", "nlinarith", "ring", "ring_nf",
    "trivial", "assumption", "contradiction", "exfalso", "use", "exists", "refine", "show", "calc",
    "funext", "ext", "subst", "injection", "positivity", "tauto", "push_neg", "by_contra", "revert",
    "generalize", "specialize", "all_goals", "any_goals", "repeat", "first", "try", "delta", "dsimp",
    "simp_arith", "norm_cast", "push_cast", "exact?", "apply?", "sorry",
]
TACTIC_RE = re.compile(r"(?<![\w'.])(" + "|".join(re.escape(t) for t in sorted(TACTICS, key=len, reverse=True)) + r")(?![\w'?])")


def _ident_re(name: str) -> re.Pattern:
    return re.compile(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'])")


def _strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def defined_identifiers(lean_text: str) -> List[str]:
    """Names introduced by def/theorem/lemma/abbrev/structure/inductive in a Lean snippet."""
    return re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*(?:def|theorem|lemma|abbrev|structure|inductive|instance)\s+([^\s(:{\[]+)", lean_text, re.M)


@dataclass
class ProofFeatures:
    proof_chars: int
    proof_lines: int
    proof_loc: int
    n_tactic_tokens: int
    count_unfold: int
    unfolds_target_function: bool
    unfold_mentions_postcond: bool
    count_simp: int
    count_simp_all: int
    simp_mentions_target_function: bool
    simp_only_used: bool
    count_rw: int
    count_have: int
    count_exact: int
    count_apply: int
    count_intro: int
    count_constructor: int
    count_cases: int
    count_induction: int
    count_split: int
    count_by_cases: int
    count_omega: int
    count_decide: int
    count_aesop: int
    count_grind: int
    count_rfl: int
    count_norm_num: int
    count_linarith: int
    uses_automation: bool
    target_function_name_occurrences: int
    code_aux_identifier_occurrences: int
    mentions_code_aux_identifier: bool
    mentions_extracted_helper_name: bool
    mentions_h_precond: bool
    proof_aux_nonempty: bool
    first_tactic: str
    tactic_histogram: Dict[str, int]

    def to_row(self) -> dict:
        d = asdict(self)
        d["tactic_histogram"] = ";".join(f"{k}={v}" for k, v in sorted(self.tactic_histogram.items()))
        return d


def extract_features(proof: str, proof_aux: str, target: str, aux_identifiers: Iterable[str] = (), helper_names: Iterable[str] = ()) -> ProofFeatures:
    raw = proof
    text = _strip_comments(proof)
    aux_text = _strip_comments(proof_aux or "")
    both = text + "\n" + aux_text
    toks = TACTIC_RE.findall(text)
    hist: Dict[str, int] = {}
    for t in toks:
        hist[t] = hist.get(t, 0) + 1

    def c(t: str) -> int:
        return hist.get(t, 0)

    # tactic argument lists for unfold / simp
    unfold_args = " ".join(re.findall(r"(?<![\w'.])unfold\b([^\n]*)", text))
    simp_args = " ".join(re.findall(r"(?<![\w'.])(?:simp_all|simp|dsimp|simp\?)\b[^\n\[]*\[([^\]]*)\]", text))
    trg = _ident_re(target)
    aux_ids = [a for a in aux_identifiers if a and a != target]
    aux_occ = sum(len(_ident_re(a).findall(both)) for a in aux_ids)
    helper_occ = sum(len(_ident_re(h).findall(both)) for h in helper_names)
    first = toks[0] if toks else ""
    automation = any(c(t) > 0 for t in ("simp", "simp_all", "aesop", "omega", "grind", "decide", "norm_num", "linarith", "nlinarith", "tauto", "native_decide"))
    return ProofFeatures(
        proof_chars=len(raw),
        proof_lines=len(raw.splitlines()),
        proof_loc=sum(1 for ln in raw.splitlines() if ln.strip() and not ln.strip().startswith("--")),
        n_tactic_tokens=len(toks),
        count_unfold=c("unfold") + c("delta"),
        unfolds_target_function=bool(trg.search(unfold_args)),
        unfold_mentions_postcond=bool(re.search(r"_postcond\b", unfold_args)),
        count_simp=c("simp") + c("simp?") + c("dsimp"),
        count_simp_all=c("simp_all"),
        simp_mentions_target_function=bool(trg.search(simp_args)),
        simp_only_used=bool(re.search(r"(?<![\w'.])simp only", text)),
        count_rw=c("rw") + c("rwa"),
        count_have=c("have"),
        count_exact=c("exact"),
        count_apply=c("apply"),
        count_intro=c("intro") + c("intros"),
        count_constructor=c("constructor"),
        count_cases=c("cases") + c("rcases") + c("obtain"),
        count_induction=c("induction"),
        count_split=c("split"),
        count_by_cases=c("by_cases"),
        count_omega=c("omega"),
        count_decide=c("decide") + c("native_decide"),
        count_aesop=c("aesop"),
        count_grind=c("grind"),
        count_rfl=c("rfl"),
        count_norm_num=c("norm_num"),
        count_linarith=c("linarith") + c("nlinarith"),
        uses_automation=automation,
        target_function_name_occurrences=len(trg.findall(both)),
        code_aux_identifier_occurrences=aux_occ,
        mentions_code_aux_identifier=aux_occ > 0,
        mentions_extracted_helper_name=helper_occ > 0,
        mentions_h_precond=bool(re.search(r"\bh_precond\b", both)),
        proof_aux_nonempty=bool(aux_text.strip()),
        first_tactic=first,
        tactic_histogram=hist,
    )
