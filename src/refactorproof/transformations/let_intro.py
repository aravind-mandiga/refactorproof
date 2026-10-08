"""T1 — whole-body ``let`` introduction (severity D, definitional).

::

    def f (...) : T :=          def f (...) : T :=
      E                   ==>     let __rp_tmp_<h> :=
                                    E
                                  __rp_tmp_<h>

The two bodies are definitionally equal by zeta reduction, so the certificate
is expected to close with ``rfl``.  The transformation is skipped when the body
carries def-level ``termination_by``/``decreasing_by`` or ``where`` clauses
(they cannot be wrapped textually) or contains a multi-line string literal
(re-indentation would change it).
"""

from __future__ import annotations

from typing import List, Optional, Tuple

from ..verina_parser import TaskBlocks
from .base import (
    Transformation,
    return_type_of_header,
    Variant,
    base_indent,
    has_def_level_termination_clause,
    has_multiline_string,
    has_where_clause,
    indent_lines,
    mentions_identifier,
    short_hash,
)


class LetIntro(Transformation):
    name = "T1_let_intro"
    severity = "D"
    equivalence_class = "definitional"
    certificate_strategy = "rfl_simp_ladder"
    certificate_laws: List[str] = []
    max_variants_per_task = 1

    def applicable(self, task: TaskBlocks) -> Tuple[bool, Optional[str]]:
        code = task.content("code")
        if not code.strip():
            return False, "empty_code_block"
        if return_type_of_header(task.def_header()) is None:
            return False, "unparseable_header"
        if has_def_level_termination_clause(code):
            return False, "def_level_termination_clause"
        if has_where_clause(code):
            return False, "where_clause"
        if has_multiline_string(code):
            return False, "multiline_string_literal"
        return True, None

    def generate(self, task: TaskBlocks, seed: int) -> List[Variant]:
        ok, _ = self.applicable(task)
        if not ok:
            return []
        code = task.content("code")
        base = base_indent(code)
        tmp = f"__rp_tmp_{short_hash(task.task_id, self.name, str(seed))}"
        if mentions_identifier(code, tmp):  # astronomically unlikely, but be safe
            return []
        body = indent_lines(code, "  ")
        if not body.endswith("\n"):
            body += "\n"
        ret = return_type_of_header(task.def_header())
        if ret is None:
            return []
        # the type ascription keeps elaboration identical to the original body (expected type drives
        # literals, coercions and instance resolution); without it `let tmp := 0` would elaborate as Nat
        new_code = f"{base}let {tmp} : {ret} :=\n{body}{base}{tmp}\n"
        return [
            self.make_variant(
                task,
                0,
                new_code,
                task.content("code_aux"),
                tmp_name=tmp,
                seed=seed,
            )
        ]
