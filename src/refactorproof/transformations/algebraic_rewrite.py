"""T3 — commutative operand swap (severity E, theorem-certified).

Rewrites one occurrence of ``A op B`` into ``B op A`` for a commutative operator
``op`` in {``+``, ``*``, ``&&``, ``||``, ``∧``, ``∨``} whose two operands are
simple atoms (identifier, numeral, indexing ``xs[i]!`` or a parenthesised group
without nested parentheses).  Nothing about the concrete type is assumed: the
variant enters the benchmark only if Lean certifies equality with the
commutativity/associativity laws listed in ``certificate_laws`` (``rfl`` is
attempted first and recorded, but is not expected to succeed).

Up to ``max_variants_per_task`` occurrences are chosen deterministically from
``(task_id, seed)``.  Occurrences inside comments or string literals are ignored.
"""

from __future__ import annotations

import random
import re
from typing import List, Optional, Tuple

from ..verina_parser import TaskBlocks
from .base import Transformation, Variant, has_multiline_string, short_hash

ATOM = r"(?:[A-Za-z_][\w'.]*(?:\[[^\[\]\n]*\]!?)?|\d+|\([^()\n]*\))"
OPS = {
    "+": r"\+",
    "*": r"\*",
    "&&": r"&&",
    "||": r"\|\|",
    "∧": r"∧",
    "∨": r"∨",
}
# operator must be a standalone token: surrounded by single spaces and not part of ++, +=, **, etc.
OCC_RE = {
    op: re.compile(
        r"(?P<pre>(?<![\w'.\]!)])|^)(?P<a>" + ATOM + r") (?P<op>" + pat + r") (?P<b>" + ATOM + r")(?![\w'(\[])",
        re.M,
    )
    for op, pat in OPS.items()
}
COMMENT_RE = re.compile(r"--.*$", re.M)

# Alternative law sets tried in order (a `first` combinator): generic Mathlib names, then core-only names
# (some VERINA tasks do not import Mathlib), then a minimal core set.
LAW_SETS = [
    ["add_comm", "add_left_comm", "add_assoc", "mul_comm", "mul_left_comm", "mul_assoc",
     "Bool.and_comm", "Bool.and_left_comm", "Bool.and_assoc", "Bool.or_comm", "Bool.or_left_comm", "Bool.or_assoc",
     "and_comm", "and_left_comm", "and_assoc", "or_comm", "or_left_comm", "or_assoc"],
    ["Nat.add_comm", "Nat.add_left_comm", "Nat.add_assoc", "Nat.mul_comm", "Nat.mul_left_comm", "Nat.mul_assoc",
     "Int.add_comm", "Int.add_left_comm", "Int.add_assoc", "Int.mul_comm", "Int.mul_left_comm", "Int.mul_assoc",
     "Bool.and_comm", "Bool.and_left_comm", "Bool.and_assoc", "Bool.or_comm", "Bool.or_left_comm", "Bool.or_assoc",
     "and_comm", "and_left_comm", "and_assoc", "or_comm", "or_left_comm", "or_assoc"],
    ["Nat.add_comm", "Int.add_comm", "Nat.mul_comm", "Int.mul_comm", "Bool.and_comm", "Bool.or_comm", "and_comm", "or_comm"],
]
LAWS = LAW_SETS[0]


def _mask(code: str) -> str:
    """Replace comment and string-literal characters with spaces (same length) so matches skip them."""
    out = list(code)
    for m in COMMENT_RE.finditer(code):
        for i in range(m.start(), m.end()):
            if out[i] != "\n":
                out[i] = " "
    masked = "".join(out)
    res = list(masked)
    in_str = False
    i = 0
    while i < len(masked):
        ch = masked[i]
        if ch == '"' and not (i > 0 and masked[i - 1] == "\\"):
            in_str = not in_str
            res[i] = " "
        elif in_str and ch != "\n":
            res[i] = " "
        i += 1
    return "".join(res)


# Lean 4 infix precedences: the swapped pair `A op B` is a complete operand pair only if the
# neighbouring tokens bind *looser* than op (or are the same op / a structural delimiter).
PREC = {"∨": 30, "||": 30, "∧": 35, "&&": 35, "+": 65, "-": 65, "*": 70, "/": 70, "%": 70,
        "<": 50, ">": 50, "<=": 50, ">=": 50, "≤": 50, "≥": 50, "=": 50, "==": 50, "!=": 50, "≠": 50,
        "↔": 20, "→": 25, "++": 65, "::": 67, "^": 75}
LEFT_DELIMS = {"(", "[", ",", ":=", "=>", "then", "else", "if", "←", "<-", "|", "return", "pure", "some"}
RIGHT_DELIMS = {")", "]", ",", "then", "else", "do", "with", ":=", "|"}
TOKEN_RE = re.compile(r"(<=|>=|==|!=|\+\+|::|<-|:=|=>|[()\[\],|]|[<>=+\-*/%^]|≤|≥|≠|∧|∨|↔|→|←|\b(?:then|else|if|do|with|return|pure|some)\b)")
KEYWORDS = {"then", "else", "if", "do", "let", "fun", "match", "with", "return", "pure", "some", "none", "true", "false"}


def _prev_token(masked: str, pos: int) -> Optional[str]:
    """Token immediately left of pos on the same line, or None at line start."""
    j = pos
    while j > 0 and masked[j - 1] == " ":
        j -= 1
    if j == 0 or masked[j - 1] == "\n":
        return None
    for m in TOKEN_RE.finditer(masked[max(0, j - 8) : j]):
        if m.end() == len(masked[max(0, j - 8) : j]):
            return m.group(1)
    return masked[j - 1]  # some other character (identifier, digit, quote ...)


def _next_token(masked: str, pos: int) -> Optional[str]:
    j = pos
    while j < len(masked) and masked[j] == " ":
        j += 1
    if j >= len(masked) or masked[j] == "\n":
        return None
    m = TOKEN_RE.match(masked, j)
    return m.group(1) if m else masked[j]


def _boundary_ok(tok: Optional[str], op: str, side: str) -> bool:
    if tok is None:
        return True
    if tok == op:
        return True
    if side == "left" and tok in LEFT_DELIMS:
        return True
    if side == "right" and tok in RIGHT_DELIMS:
        return True
    if tok in PREC:
        p_op, p_tok = PREC[op], PREC[tok]
        if p_tok < p_op:
            return True
        # same precedence, left-associative arithmetic on the right side is safe: (A op B) tok C
        if side == "right" and p_tok == p_op and op in ("+", "*") and tok in ("-", "/", "%"):
            return True
        return False
    return False  # identifier / literal / unknown → possibly function application, be conservative


def find_occurrences(code: str) -> List[Tuple[int, int, str, str, str]]:
    """Return (start, end, a, op, b) for every eligible occurrence, in textual order."""
    masked = _mask(code)
    occs = []
    for op, rx in OCC_RE.items():
        for m in rx.finditer(masked):
            a, b = m.group("a"), m.group("b")
            if a == b:
                continue  # swapping identical operands is a no-op
            if a in KEYWORDS or b in KEYWORDS:
                continue
            if not _boundary_ok(_prev_token(masked, m.start("a")), op, "left"):
                continue
            if not _boundary_ok(_next_token(masked, m.end("b")), op, "right"):
                continue
            occs.append((m.start("a"), m.end("b"), a, op, b))
    # drop overlapping occurrences (keep earliest)
    occs.sort()
    kept = []
    last_end = -1
    for o in occs:
        if o[0] >= last_end:
            kept.append(o)
            last_end = o[1]
    return kept


class CommutativeSwap(Transformation):
    name = "T3_comm_swap"
    severity = "E"
    equivalence_class = "theorem_certified"
    certificate_strategy = "rfl_simp_ladder"
    certificate_laws = LAWS
    max_variants_per_task = 3

    def applicable(self, task: TaskBlocks) -> Tuple[bool, Optional[str]]:
        code = task.content("code")
        if not code.strip():
            return False, "empty_code_block"
        if has_multiline_string(code):
            return False, "multiline_string_literal"
        if not find_occurrences(code):
            return False, "no_commutative_operator_occurrence"
        return True, None

    def generate(self, task: TaskBlocks, seed: int) -> List[Variant]:
        ok, _ = self.applicable(task)
        if not ok:
            return []
        code = task.content("code")
        occs = find_occurrences(code)
        rng = random.Random(int(short_hash(task.task_id, self.name, str(seed), n=16), 16))
        chosen = sorted(rng.sample(range(len(occs)), min(self.max_variants_per_task, len(occs))))
        variants = []
        for k, idx in enumerate(chosen):
            s, e, a, op, b = occs[idx]
            new_code = code[:s] + f"{b} {op} {a}" + code[e:]
            assert new_code != code
            variants.append(
                self.make_variant(
                    task,
                    k,
                    new_code,
                    task.content("code_aux"),
                    law_sets=LAW_SETS,
                    extra_levels=[["ac_rfl", "(try simp only [{DEFS}]) <;> (try ac_nf) <;> {CLOSER}"]],
                    operator=op,
                    lhs=a,
                    rhs=b,
                    occurrence_index=idx,
                    n_eligible_occurrences=len(occs),
                    char_offset=s,
                    seed=seed,
                )
            )
        return variants
