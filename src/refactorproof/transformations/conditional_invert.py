"""T4 — conditional branch inversion (severity E, theorem-certified).

::

    if c then A else B      ==>      if ¬ (c) then B else A

Applied to the outermost ``if`` that forms the tail expression of the body: the
``if`` keyword starts a line at the body's base indentation, and its ``then``
and ``else`` are found at bracket depth zero (``else if`` chains are treated as
nested, so only the first branch pair is inverted).  Dependent conditionals
(``if h : c then``) and bodies containing ``do`` blocks are skipped.  The
certificate law is ``ite_not``; Lean decides validity.
"""

from __future__ import annotations

import re
from typing import List, Optional, Tuple

from ..verina_parser import TaskBlocks
from .base import DO_RE, Transformation, Variant, base_indent, has_def_level_termination_clause, has_multiline_string, has_where_clause

KW_RE = re.compile(r"(?<![\w'.])(if|then|else)(?![\w'])")


def _mask(code: str) -> str:
    out = list(code)
    # comments
    for m in re.finditer(r"--.*$", code, re.M):
        for i in range(m.start(), m.end()):
            if out[i] != "\n":
                out[i] = " "
    s = "".join(out)
    res = list(s)
    in_str = False
    for i, ch in enumerate(s):
        if ch == '"' and not (i > 0 and s[i - 1] == "\\"):
            in_str = not in_str
            res[i] = " "
        elif in_str and ch != "\n":
            res[i] = " "
    return "".join(res)


def find_tail_if(code: str) -> Optional[Tuple[int, int, int, int]]:
    """Return (if_pos, then_pos, else_pos, end) of the outermost tail-position ``if``."""
    masked = _mask(code)
    base = base_indent(code)
    # candidate: an `if` at line start with base indentation
    cand = None
    for m in re.finditer(r"^(?P<ind>[ \t]*)if(?![\w'])", masked, re.M):
        if m.group("ind") == base:
            cand = m.start() + len(base)
            break
    if cand is None:
        return None
    # scan keywords from cand with depth tracking
    depth = 0
    stack: List[int] = []
    then_pos = else_pos = None
    i = cand
    while i < len(masked):
        ch = masked[i]
        if ch in "([{":
            depth += 1
            i += 1
            continue
        if ch in ")]}":
            depth -= 1
            if depth < 0:
                return None
            i += 1
            continue
        if depth == 0:
            m = KW_RE.match(masked, i)
            if m:
                kw = m.group(1)
                if kw == "if":
                    stack.append(i)
                elif kw == "then":
                    if not stack:
                        return None
                    if len(stack) == 1 and then_pos is None:
                        then_pos = i
                elif kw == "else":
                    if not stack:
                        return None
                    if len(stack) == 1 and else_pos is None:
                        else_pos = i
                        stack.pop()
                        break
                    stack.pop()
                i = m.end()
                continue
        i += 1
    if then_pos is None or else_pos is None:
        return None
    return cand, then_pos, else_pos, len(code)


class ConditionalInvert(Transformation):
    name = "T4_cond_invert"
    severity = "E"
    equivalence_class = "theorem_certified"
    certificate_strategy = "rfl_simp_ladder"
    certificate_laws = ["ite_not"]
    max_variants_per_task = 1

    def applicable(self, task: TaskBlocks) -> Tuple[bool, Optional[str]]:
        code = task.content("code")
        if not code.strip():
            return False, "empty_code_block"
        if has_def_level_termination_clause(code):
            return False, "def_level_termination_clause"
        if has_where_clause(code):
            return False, "where_clause"
        if has_multiline_string(code):
            return False, "multiline_string_literal"
        if DO_RE.search(code):
            return False, "do_block"
        pos = find_tail_if(code)
        if pos is None:
            return False, "no_tail_if_then_else"
        if_pos, then_pos, _, _ = pos
        cond = code[if_pos + 2 : then_pos].strip()
        if re.match(r"^[A-Za-z_][\w']*\s*:", cond):
            return False, "dependent_if"
        if not cond:
            return False, "empty_condition"
        return True, None

    def generate(self, task: TaskBlocks, seed: int) -> List[Variant]:
        ok, _ = self.applicable(task)
        if not ok:
            return []
        code = task.content("code")
        if_pos, then_pos, else_pos, end = find_tail_if(code)
        base = base_indent(code)
        cond = code[if_pos + 2 : then_pos].strip()
        a_text = code[then_pos + 4 : else_pos]  # between `then` and `else`
        b_text = code[else_pos + 4 : end]  # after `else` to end of body
        prefix = code[:if_pos]
        a_multiline = "\n" in a_text.strip("\n") or a_text.startswith("\n") or a_text.lstrip(" ").startswith("\n")
        a_body = a_text.rstrip()
        b_body = b_text.rstrip("\n")
        if not b_body.startswith("\n") and not b_body.startswith(" "):
            b_body = " " + b_body
        if not a_body.startswith("\n") and not a_body.startswith(" "):
            a_body = " " + a_body
        new_code = f"{prefix}if ¬ ({cond}) then{b_body}\n{base}else{a_body}\n"
        assert new_code != code
        return [
            self.make_variant(
                task,
                0,
                new_code,
                task.content("code_aux"),
                law_sets=[["ite_not"], ["ite_not", "Bool.not_eq_true", "decide_not", "Nat.not_lt", "Nat.not_le", "Int.not_lt", "Int.not_le"]],
                extra_levels=[
                    ["bycases", f"by_cases h : ({cond}) <;> (try simp [h, {{DEFS}}]) <;> {{CLOSER}}"],
                    ["bycases_ite", f"by_cases h : ({cond}) <;> (try simp [h, ite_not, {{DEFS}}]) <;> {{CLOSER}}"],
                    ["split_simp_all", "simp only [{DEFS}]; split <;> (try simp_all) <;> {CLOSER}"],
                ],
                condition=cond,
                then_multiline=a_multiline,
                seed=seed,
            )
        ]
