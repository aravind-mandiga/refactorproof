"""Marker-based parser for VERINA ``task.lean`` files.

VERINA delimits regions with comment markers of the form::

    -- !benchmark @start <name> [key=value ...]
    ...
    -- !benchmark @end <name>

This module splits a file into an alternating sequence of verbatim text
segments and marker-delimited blocks, such that ``render(parse(src)) == src``
byte-for-byte.  It deliberately does *not* parse Lean syntax; the only
structural assumption is the marker grammar above, matched on whole tokens
(so ``code`` never matches ``code_aux``).

Block names present in the dataset: ``import`` (possibly several, distinguished
by ``type=...``), ``task_aux``, ``solution_aux``, ``precond_aux``, ``precond``,
``code_aux``, ``code``, ``postcond_aux``, ``postcond``, ``proof_aux``, ``proof``.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Union

MARKER_RE = re.compile(
    r"^(?P<indent>[ \t]*)-- !benchmark @(?P<kind>start|end)[ \t]+(?P<name>\w+)(?P<args>[^\r\n]*)(?P<eol>\r?\n?)$"
)

REQUIRED_BLOCKS = (
    "import",
    "solution_aux",
    "precond_aux",
    "precond",
    "code_aux",
    "code",
    "postcond_aux",
    "postcond",
    "proof_aux",
    "proof",
)

SPEC_BLOCKS = ("precond_aux", "precond", "postcond_aux", "postcond")
HOLE_RE = re.compile(r"(?<![\w'.])(sorry|admit)(?![\w'])")


class ParseError(ValueError):
    pass


@dataclass(frozen=True)
class Block:
    """One marker-delimited region, stored verbatim."""

    name: str
    args: Dict[str, str]
    start_line: str  # full marker line including indentation and newline
    content: str  # everything strictly between start_line and end_line
    end_line: str  # full marker line including indentation and newline (may lack newline at EOF)

    @property
    def key(self) -> str:
        """Lookup key: plain name, or ``import:<type>`` for typed import blocks."""
        if self.name == "import":
            return f"import:{self.args.get('type', '')}"
        return self.name

    def render(self) -> str:
        return self.start_line + self.content + self.end_line

    def stripped(self) -> str:
        return self.content.strip()

    def sha256(self) -> str:
        return hashlib.sha256(self.content.encode("utf-8")).hexdigest()

    def has_hole(self) -> bool:
        return HOLE_RE.search(self.content) is not None


Segment = Union[str, Block]


@dataclass(frozen=True)
class Signature:
    name: str
    parameters: List[Dict[str, str]]
    return_type: str

    @staticmethod
    def from_task_json(d: dict) -> "Signature":
        s = d["signature"]
        return Signature(
            name=s["name"],
            parameters=[dict(p) for p in s.get("parameters", [])],
            return_type=s["return_type"],
        )


@dataclass(frozen=True)
class TaskBlocks:
    task_id: str
    segments: List[Segment]
    signature: Optional[Signature] = None
    source_path: Optional[Path] = None
    task_json: Optional[dict] = field(default=None, repr=False)

    # ------------------------------------------------------------------ core
    def render(self) -> str:
        return "".join(s if isinstance(s, str) else s.render() for s in self.segments)

    @property
    def blocks(self) -> Dict[str, Block]:
        out: Dict[str, Block] = {}
        for s in self.segments:
            if isinstance(s, Block):
                if s.key in out:
                    raise ParseError(f"{self.task_id}: duplicate block {s.key}")
                out[s.key] = s
        return out

    def block(self, key: str) -> Block:
        if key == "import":
            key = "import:solution"
        try:
            return self.blocks[key]
        except KeyError:
            raise KeyError(f"{self.task_id}: no block {key!r}; have {sorted(self.blocks)}")

    def has_block(self, key: str) -> bool:
        if key == "import":
            key = "import:solution"
        return key in self.blocks

    def content(self, key: str) -> str:
        return self.block(key).content

    def with_block_content(self, key: str, new_content: str) -> "TaskBlocks":
        """Return a copy with one block's content replaced (markers untouched)."""
        if key == "import":
            key = "import:solution"
        found = False
        new_segments: List[Segment] = []
        for s in self.segments:
            if isinstance(s, Block) and s.key == key:
                new_segments.append(replace(s, content=new_content))
                found = True
            else:
                new_segments.append(s)
        if not found:
            raise KeyError(f"{self.task_id}: no block {key!r}")
        return replace(self, segments=new_segments)

    def text_before(self, key: str) -> str:
        """Verbatim text segment immediately preceding block ``key``."""
        if key == "import":
            key = "import:solution"
        prev = ""
        for s in self.segments:
            if isinstance(s, Block):
                if s.key == key:
                    return prev
                prev = ""
            else:
                prev = s
        raise KeyError(key)

    # -------------------------------------------------------------- semantics
    @property
    def function_name(self) -> str:
        if self.signature is not None:
            return self.signature.name
        return self.def_header_name() or ""

    def def_header(self) -> str:
        """The ``def ... :=`` header text that precedes the ``code`` block.

        Taken from the raw text segment before the code marker: the tail of that
        segment starting at the last line that begins with ``def``/``partial def``.
        """
        before = self.text_before("code")
        lines = before.splitlines(keepends=True)
        start = None
        for i, ln in enumerate(lines):
            if re.match(r"^\s*(?:@\[[^\]]*\]\s*)?(?:partial\s+|noncomputable\s+)?def\s", ln):
                start = i
        if start is None:
            return ""
        return "".join(lines[start:])

    def def_header_name(self) -> Optional[str]:
        m = re.search(r"def\s+([^\s(:{\[]+)", self.def_header())
        return m.group(1) if m else None

    def with_def_header(self, new_header: str) -> "TaskBlocks":
        """Replace the ``def ... :=`` header text that precedes the code block (raw text segment)."""
        old = self.def_header()
        if not old:
            raise ValueError(f"{self.task_id}: no def header found")
        new_segments: List[Segment] = []
        prev_idx: Optional[int] = None
        for i, s in enumerate(self.segments):
            if isinstance(s, Block) and s.key == "code":
                break
            if isinstance(s, str):
                prev_idx = i
        else:
            raise KeyError("code")
        assert prev_idx is not None
        text = self.segments[prev_idx]
        pos = text.rfind(old)
        assert pos >= 0
        new_text = text[:pos] + new_header + text[pos + len(old):]
        new_segments = list(self.segments)
        new_segments[prev_idx] = new_text
        return replace(self, segments=new_segments)


    def spec_hash(self) -> str:
        """SHA-256 over the concatenated spec blocks (Invariant A)."""
        h = hashlib.sha256()
        for k in SPEC_BLOCKS:
            h.update(k.encode())
            h.update(b"\0")
            h.update(self.content(k).encode("utf-8"))
            h.update(b"\0")
        return h.hexdigest()

    def proof_hash(self) -> str:
        """SHA-256 over proof_aux + proof blocks (Invariant B)."""
        h = hashlib.sha256()
        for k in ("proof_aux", "proof"):
            h.update(k.encode())
            h.update(b"\0")
            h.update(self.content(k).encode("utf-8"))
            h.update(b"\0")
        return h.hexdigest()

    def has_reference_proof_text(self) -> bool:
        """Text-level check: proof block non-empty and free of sorry/admit."""
        p = self.block("proof")
        return p.stripped() != "" and not p.has_hole() and not self.block("proof_aux").has_hole()

    def loc(self, key: str) -> int:
        return sum(1 for ln in self.content(key).splitlines() if ln.strip() and not ln.strip().startswith("--"))


# ---------------------------------------------------------------------- parse
def parse_source(src: str, task_id: str = "<unknown>") -> List[Segment]:
    lines = src.splitlines(keepends=True)
    segments: List[Segment] = []
    text_buf: List[str] = []
    cur_name: Optional[str] = None
    cur_args: Dict[str, str] = {}
    cur_start: str = ""
    cur_content: List[str] = []

    for lineno, line in enumerate(lines, 1):
        m = MARKER_RE.match(line)
        if m is None:
            if cur_name is None:
                text_buf.append(line)
            else:
                cur_content.append(line)
            continue
        kind, name, args_str = m.group("kind"), m.group("name"), m.group("args")
        if kind == "start":
            if cur_name is not None:
                raise ParseError(f"{task_id}:{lineno}: nested @start {name} inside {cur_name}")
            args: Dict[str, str] = {}
            for tok in args_str.split():
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    args[k] = v
                else:
                    args[tok] = ""
            if text_buf:
                segments.append("".join(text_buf))
                text_buf = []
            cur_name, cur_args, cur_start, cur_content = name, args, line, []
        else:  # end
            if cur_name is None or name != cur_name:
                raise ParseError(f"{task_id}:{lineno}: @end {name} does not close {cur_name}")
            segments.append(
                Block(name=cur_name, args=cur_args, start_line=cur_start, content="".join(cur_content), end_line=line)
            )
            cur_name = None
    if cur_name is not None:
        raise ParseError(f"{task_id}: unterminated block {cur_name}")
    if text_buf:
        segments.append("".join(text_buf))
    return segments


def parse_task_source(src: str, task_id: str, signature: Optional[Signature] = None) -> TaskBlocks:
    tb = TaskBlocks(task_id=task_id, segments=parse_source(src, task_id), signature=signature)
    missing = [b for b in REQUIRED_BLOCKS if not tb.has_block(b)]
    if missing:
        raise ParseError(f"{task_id}: missing blocks {missing}")
    return tb


def load_task(task_dir: Path) -> TaskBlocks:
    task_dir = Path(task_dir)
    tj = json.loads((task_dir / "task.json").read_text(encoding="utf-8"))
    lean_path = task_dir / tj.get("lean_file", "./task.lean")
    src = lean_path.read_text(encoding="utf-8")
    sig = Signature.from_task_json(tj)
    tb = parse_task_source(src, tj["id"], sig)
    return replace(tb, source_path=lean_path, task_json=tj)


def iter_task_dirs(verina_root: Path) -> List[Path]:
    ds = Path(verina_root) / "datasets" / "verina"
    dirs = [d for d in ds.iterdir() if d.is_dir() and d.name.startswith("verina_")]
    return sorted(dirs, key=lambda d: (d.name.split("_")[1], int(d.name.split("_")[-1])))


def tier_of(task_id: str) -> str:
    return "basic" if "_basic_" in task_id else "advanced"


DEF_MODIFIERS = ("noncomputable", "private", "protected", "partial", "unsafe")


def add_def_modifier(header: str, modifier: str) -> str:
    """Insert ``modifier`` right before ``def`` (after any attribute list), unless already present."""
    if re.search(r"(?<![\w])" + modifier + r"\s+def\b", header):
        return header
    return re.sub(r"((?:@\[[^\]]*\]\s*)?)((?:(?:" + "|".join(DEF_MODIFIERS) + r")\s+)*)def\b", lambda m: m.group(1) + m.group(2) + modifier + " def", header, count=1)


def strip_def_modifiers(header: str) -> str:
    """Header with all def modifiers removed (for Invariant F comparisons: name + signature only)."""
    return re.sub(r"(?<![\w])(?:" + "|".join(DEF_MODIFIERS) + r")\s+(?=(?:(?:" + "|".join(DEF_MODIFIERS) + r")\s+)*def\b)", "", header)


__all__ = [
    "Block",
    "TaskBlocks",
    "Signature",
    "ParseError",
    "parse_source",
    "parse_task_source",
    "load_task",
    "iter_task_dirs",
    "tier_of",
    "add_def_modifier",
    "strip_def_modifiers",
    "REQUIRED_BLOCKS",
    "SPEC_BLOCKS",
]
