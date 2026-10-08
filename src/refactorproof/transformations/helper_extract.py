"""T2 — whole-body helper extraction (severity S, structural).

::

    def f (x : A) (h_precond : f_precond x) : T :=
      E
                    ==>
    private def f__rp_helper_<h> (x : A) (h_precond : f_precond x) : T :=
      E                                                     -- placed in code_aux

    def f (x : A) (h_precond : f_precond x) : T :=
      f__rp_helper_<h> x h_precond

``f`` and the helper are delta/beta-equivalent, so ``rfl`` is expected to
close the certificate, yet tactics such as ``unfold f`` or ``simp [f]`` now
expose an opaque helper application instead of the body.

The public name and signature of ``f`` are preserved verbatim (Invariant F).
Skipped when: the body refers to ``f`` itself (recursive definitions would
need renaming), the header has implicit/instance binders we cannot forward
positionally, or the body carries def-level termination/``where`` clauses.
"""

from __future__ import annotations

import re
from typing import List, Optional, Tuple

from ..verina_parser import TaskBlocks
from .base import (
    Transformation,
    Variant,
    base_indent,
    has_def_level_termination_clause,
    has_where_clause,
    mentions_identifier,
    short_hash,
)

EXPLICIT_BINDER_RE = re.compile(r"\(\s*([^\s:()]+(?:\s+[^\s:()]+)*)\s*:")


def parse_header(header: str):
    """Return (name, binder_names, attrs) for a one-line ``def name binders : T :=`` header."""
    h = header.strip()
    if "\n" in h:
        return None
    m = re.match(r"^(?P<attrs>(?:@\[[^\]]*\]\s*)?)(?P<mods>(?:(?:private|protected|noncomputable|partial)\s+)*)def\s+(?P<name>[^\s(:{\[]+)\s*(?P<rest>.*):=$", h)
    if not m:
        return None
    rest = m.group("rest")
    # reject implicit / instance / strict-implicit binders
    if re.search(r"(^|\s)[{\[⦃]", rest.split(" : ")[0] if " : " in rest else rest):
        # a '{' or '[' that starts a binder group (not inside parentheses of a type)
        depth = 0
        for ch in rest:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            elif ch in "{[⦃" and depth == 0:
                return None
    binders: List[str] = []
    depth = 0
    i = 0
    # walk top-level parenthesised binder groups until the return-type colon
    while i < len(rest):
        ch = rest[i]
        if ch == "(" and depth == 0:
            j = i
            d = 0
            while j < len(rest):
                if rest[j] == "(":
                    d += 1
                elif rest[j] == ")":
                    d -= 1
                    if d == 0:
                        break
                j += 1
            group = rest[i + 1 : j]
            if ":" not in group:
                return None
            names = group.split(":", 1)[0].split()
            if not names or any(not re.match(r"^[^\s():{}\[\]]+$", n) for n in names):
                return None
            binders.extend(names)
            i = j + 1
            continue
        if ch == ":" and depth == 0:
            break
        i += 1
    return m.group("name"), binders, m.group("attrs").strip(), m.group("mods").strip()


class HelperExtract(Transformation):
    name = "T2_helper_extract"
    severity = "S"
    equivalence_class = "definitional"
    certificate_strategy = "rfl_simp_ladder"
    certificate_laws: List[str] = []
    max_variants_per_task = 1

    def applicable(self, task: TaskBlocks) -> Tuple[bool, Optional[str]]:
        code = task.content("code")
        if not code.strip():
            return False, "empty_code_block"
        if has_def_level_termination_clause(code):
            return False, "def_level_termination_clause"
        if has_where_clause(code):
            return False, "where_clause"
        header = task.def_header()
        parsed = parse_header(header)
        if parsed is None:
            return False, "unparseable_or_implicit_header"
        name, binders, attrs, mods = parsed
        if task.signature and name != task.signature.name:
            return False, "header_name_mismatch"
        if not binders:
            return False, "no_explicit_binders"
        if mentions_identifier(code, name):
            return False, "self_recursive_body"
        if "partial" in mods:
            return False, "partial_def"
        return True, None

    def generate(self, task: TaskBlocks, seed: int) -> List[Variant]:
        ok, _ = self.applicable(task)
        if not ok:
            return []
        code = task.content("code")
        header = task.def_header()
        name, binders, attrs, mods = parse_header(header)
        helper = f"{name}__rp_helper_{short_hash(task.task_id, self.name, str(seed))}"
        if mentions_identifier(code, helper) or mentions_identifier(task.content("code_aux"), helper):
            return []
        # helper header: same binders/return type, new name, private, no attributes
        h = header.strip()
        h_wo_attrs = h[len(attrs):].lstrip() if attrs else h
        helper_header = re.sub(r"^(?:(?:private|protected|noncomputable)\s+)*def\s+" + re.escape(name), f"private def {helper}", h_wo_attrs, count=1)
        if "noncomputable" in mods:
            helper_header = "noncomputable " + helper_header
        body = code if code.endswith("\n") else code + "\n"
        helper_def = helper_header + "\n" + body
        old_aux = task.content("code_aux")
        if old_aux.strip():
            new_aux = old_aux.rstrip("\n") + "\n\n" + helper_def
        else:
            new_aux = "\n" + helper_def
        base = base_indent(code)
        new_code = f"{base}{helper} {' '.join(binders)}\n"
        return [
            self.make_variant(
                task,
                0,
                new_code,
                new_aux,
                helper_names=[helper],
                binders=binders,
                seed=seed,
            )
        ]
