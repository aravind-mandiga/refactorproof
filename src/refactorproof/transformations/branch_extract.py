"""T5 — else-branch extraction (severity S, definitional).

::

    def f xs h : T :=            def f xs h : T :=
      if c then                    if c then
        A                            A
      else                         else
        B                            f__rp_branch_<h> xs h
                                   private def f__rp_branch_<h> xs h : T := B      (in code_aux)

Applies only when the body *starts* with the tail ``if`` (no preceding ``let`` bindings), so the
``else`` branch is closed over the definition's parameters and can be moved into a helper with the
same binders.  Like T2 the helper is delta-equivalent, but the structural change is partial: the
conditional stays in place and only one branch becomes an opaque application.  Proofs that
``unfold f`` and then ``split`` see the helper where the branch body used to be.
"""

from __future__ import annotations

import re
from typing import List, Optional, Tuple

from ..verina_parser import TaskBlocks
from .base import DO_RE, LET_REC_RE, Transformation, Variant, base_indent, has_def_level_termination_clause, has_multiline_string, has_where_clause, indent_lines, mentions_identifier, short_hash
from .conditional_invert import find_tail_if
from .helper_extract import parse_header


class BranchExtract(Transformation):
    name = "T5_branch_extract"
    severity = "S"
    equivalence_class = "definitional"
    certificate_strategy = "rfl_simp_ladder"
    certificate_laws: List[str] = []
    max_variants_per_task = 1

    def _analyse(self, task: TaskBlocks):
        code = task.content("code")
        if not code.strip():
            return None, "empty_code_block"
        if has_def_level_termination_clause(code):
            return None, "def_level_termination_clause"
        if has_where_clause(code):
            return None, "where_clause"
        if has_multiline_string(code):
            return None, "multiline_string_literal"
        if DO_RE.search(code):
            return None, "do_block"
        parsed = parse_header(task.def_header())
        if parsed is None:
            return None, "unparseable_or_implicit_header"
        name, binders, attrs, mods = parsed
        if task.signature and name != task.signature.name:
            return None, "header_name_mismatch"
        if not binders:
            return None, "no_explicit_binders"
        if "partial" in mods:
            return None, "partial_def"
        if mentions_identifier(code, name):
            return None, "self_recursive_body"
        pos = find_tail_if(code)
        if pos is None:
            return None, "no_tail_if_then_else"
        if_pos, then_pos, else_pos, end = pos
        if code[:if_pos].strip():
            return None, "bindings_before_tail_if"  # branch would not be closed over the parameters
        cond = code[if_pos + 2 : then_pos].strip()
        if re.match(r"^[A-Za-z_][\w']*\s*:", cond):
            return None, "dependent_if"
        branch = code[else_pos + 4 : end]
        if not branch.strip():
            return None, "empty_else_branch"
        if LET_REC_RE.search(branch):
            return None, "let_rec_in_branch"
        return (code, name, binders, attrs, mods, if_pos, then_pos, else_pos, end), None

    def applicable(self, task: TaskBlocks) -> Tuple[bool, Optional[str]]:
        info, reason = self._analyse(task)
        return (info is not None), reason

    def generate(self, task: TaskBlocks, seed: int) -> List[Variant]:
        info, _ = self._analyse(task)
        if info is None:
            return []
        code, name, binders, attrs, mods, if_pos, then_pos, else_pos, end = info
        helper = f"{name}__rp_branch_{short_hash(task.task_id, self.name, str(seed))}"
        if mentions_identifier(code, helper) or mentions_identifier(task.content("code_aux"), helper):
            return []
        header = task.def_header().strip()
        h_wo_attrs = header[len(attrs):].lstrip() if attrs else header
        helper_header = re.sub(r"^(?:(?:private|protected|noncomputable)\s+)*def\s+" + re.escape(name), f"private def {helper}", h_wo_attrs, count=1)
        if "noncomputable" in mods:
            helper_header = "noncomputable " + helper_header
        # helper body: the else branch, dedented to the body's base indentation
        branch = code[else_pos + 4 : end].strip("\n")
        lines = branch.splitlines()
        nb = [ln for ln in lines if ln.strip()]
        common = min(len(ln) - len(ln.lstrip(" ")) for ln in nb)
        body = "\n".join((ln[common:] if ln.strip() else "") for ln in lines)
        base = base_indent(code)
        body = indent_lines(body + "\n", base)
        helper_def = helper_header + "\n" + body
        old_aux = task.content("code_aux")
        new_aux = (old_aux.rstrip("\n") + "\n\n" + helper_def) if old_aux.strip() else ("\n" + helper_def)
        else_kw_end = else_pos + 4
        new_code = code[:else_kw_end] + "\n" + base + "  " + f"{helper} {' '.join(binders)}" + "\n"
        assert new_code != code
        return [
            self.make_variant(
                task,
                0,
                new_code,
                new_aux,
                helper_names=[helper],
                binders=binders,
                extracted="else_branch",
                seed=seed,
            )
        ]
