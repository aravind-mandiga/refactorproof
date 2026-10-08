"""Transformation interface, Variant and CandidateRecord data model.

All transformations are deterministic text rewrites of the ``code`` (and,
where needed, ``code_aux``) block of a VERINA task.  They never touch the
specification or proof blocks and never call a model.  Whether a candidate is
*behavior preserving* is decided later by Lean (see ``certify.py``); the
transformation itself only proposes.
"""

from __future__ import annotations

import hashlib
import re
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass, field
from typing import Dict, List, Optional, Tuple

from ..verina_parser import TaskBlocks

SEVERITIES = ("D", "S", "E")
EQUIVALENCE_CLASSES = ("definitional", "theorem_certified")


@dataclass
class Variant:
    task_id: str
    variant_id: str
    transformation: str
    severity: str
    equivalence_class: str
    transformed_code: str
    transformed_code_aux: str
    certificate_strategy: str
    certificate_laws: List[str] = field(default_factory=list)
    helper_names: List[str] = field(default_factory=list)
    metadata: Dict = field(default_factory=dict)
    extra_levels: List[List[str]] = field(default_factory=list)  # [[level_name, tactic script using {DEFS}], ...]

    def to_json(self) -> dict:
        return asdict(self)

    @staticmethod
    def from_json(d: dict) -> "Variant":
        return Variant(**d)


@dataclass
class CandidateRecord:
    """One row of the candidate manifest: every attempted (task, transformation) pair."""

    task_id: str
    tier: str
    transformation: str
    severity: str
    equivalence_class: str
    applicable: bool
    inapplicable_reason: Optional[str]
    candidate_generated: bool
    n_variants: int
    variant_ids: List[str]
    code_loc_original: int
    code_loc_refactored: Optional[int]
    structural_metadata: Dict = field(default_factory=dict)

    def to_json(self) -> dict:
        return asdict(self)


def short_hash(*parts: str, n: int = 8) -> str:
    h = hashlib.sha256("\0".join(parts).encode("utf-8")).hexdigest()
    return h[:n]


def base_indent(text: str) -> str:
    """Common leading whitespace of non-blank lines (VERINA bodies use two spaces)."""
    indents = [len(ln) - len(ln.lstrip(" ")) for ln in text.splitlines() if ln.strip()]
    if not indents:
        return "  "
    return " " * min(indents)


def indent_lines(text: str, extra: str) -> str:
    out = []
    for ln in text.splitlines(keepends=True):
        out.append(extra + ln if ln.strip() else ln)
    return "".join(out)


def count_loc(text: str) -> int:
    return sum(1 for ln in text.splitlines() if ln.strip() and not ln.strip().startswith("--"))


# --- structural predicates shared by several transformations -----------------
DEF_LEVEL_CLAUSE_RE = re.compile(r"^(?P<ind>[ \t]*)(termination_by|decreasing_by)\b", re.M)
WHERE_RE = re.compile(r"^[ \t]*where\b", re.M)
DO_RE = re.compile(r"\bdo\b")
LET_REC_RE = re.compile(r"\blet\s+rec\b")


def has_def_level_termination_clause(code: str) -> bool:
    """``termination_by``/``decreasing_by`` at the body's base indentation belong to the
    enclosing ``def`` and cannot be wrapped or moved textually."""
    base = base_indent(code)
    for m in DEF_LEVEL_CLAUSE_RE.finditer(code):
        if len(m.group("ind")) <= len(base):
            return True
    return False


def has_where_clause(code: str) -> bool:
    return WHERE_RE.search(code) is not None


def mentions_identifier(text: str, ident: str) -> bool:
    return re.search(r"(?<![\w.'])" + re.escape(ident) + r"(?![\w'])", text) is not None


def has_multiline_string(code: str) -> bool:
    # a string literal that spans lines would be damaged by re-indentation
    in_str = False
    for ch in code:
        if ch == '"':
            in_str = not in_str
        elif ch == "\n" and in_str:
            return True
    return False


class Transformation(ABC):
    name: str = "base"
    severity: str = "D"
    equivalence_class: str = "definitional"
    certificate_strategy: str = "rfl_simp_ladder"
    certificate_laws: List[str] = []
    max_variants_per_task: int = 1

    @abstractmethod
    def applicable(self, task: TaskBlocks) -> Tuple[bool, Optional[str]]:
        """Return (True, None) if the transformation can be attempted, else (False, reason)."""

    @abstractmethod
    def generate(self, task: TaskBlocks, seed: int) -> List[Variant]:
        """Deterministically produce candidate variants (may be empty)."""

    # helpers ---------------------------------------------------------------
    def variant_id(self, task: TaskBlocks, k: int) -> str:
        return f"{task.task_id}__{self.name}__{k}"

    def make_variant(self, task: TaskBlocks, k: int, code: str, code_aux: str, **meta) -> Variant:
        helper_names = meta.pop("helper_names", [])
        extra_levels = meta.pop("extra_levels", [])
        return Variant(
            task_id=task.task_id,
            variant_id=self.variant_id(task, k),
            transformation=self.name,
            severity=self.severity,
            equivalence_class=self.equivalence_class,
            transformed_code=code,
            transformed_code_aux=code_aux,
            certificate_strategy=self.certificate_strategy,
            certificate_laws=list(self.certificate_laws),
            helper_names=list(helper_names),
            metadata=meta,
            extra_levels=[list(x) for x in extra_levels],
        )

    def record(self, task: TaskBlocks, applicable: bool, reason: Optional[str], variants: List[Variant]) -> CandidateRecord:
        from ..verina_parser import tier_of

        code = task.content("code")
        return CandidateRecord(
            task_id=task.task_id,
            tier=tier_of(task.task_id),
            transformation=self.name,
            severity=self.severity,
            equivalence_class=self.equivalence_class,
            applicable=applicable,
            inapplicable_reason=reason,
            candidate_generated=len(variants) > 0,
            n_variants=len(variants),
            variant_ids=[v.variant_id for v in variants],
            code_loc_original=count_loc(code),
            code_loc_refactored=(count_loc(variants[0].transformed_code) + count_loc(variants[0].transformed_code_aux) - count_loc(task.content("code_aux"))) if variants else None,
            structural_metadata={
                "code_has_def_level_termination": has_def_level_termination_clause(code),
                "code_has_where": has_where_clause(code),
                "code_has_do": DO_RE.search(code) is not None,
                "code_has_let_rec": LET_REC_RE.search(code) is not None,
                "code_self_recursive": mentions_identifier(code, task.signature.name) if task.signature else False,
                "code_aux_nonempty": task.content("code_aux").strip() != "",
                "n_if": len(re.findall(r"\bif\b", code)),
                "n_plus": code.count("+") - code.count("++") * 2,
            },
        )


def return_type_of_header(header: str) -> Optional[str]:
    """Return type text of a one-line ``def name binders : T :=`` header (None if unparseable)."""
    h = header.strip()
    m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*def\s+[^\s(:{\[]+\s*(?P<rest>.*):=$", h, re.S)
    if not m:
        return None
    rest = m.group("rest").strip()
    depth = 0
    for i, ch in enumerate(rest):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            ret = rest[i + 1 :].strip()
            return ret or None
    return None
