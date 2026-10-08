"""Subprocess wrapper around the pinned VERINA Lean environment.

Every compile is run as ``lake env lean <file>`` with the VERINA checkout as the
working directory, so ``import Mathlib`` resolves against the pinned
``lake-manifest.json``.  The full command, exit code, stdout/stderr, elapsed
time and parsed diagnostics are recorded for every invocation.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import List, Optional

MSG_RE = re.compile(r"^(?P<file>[^\n:]+):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info): ?(?P<msg>.*)$")

FAILURE_CATEGORIES = (
    "unknown_constant_or_identifier",
    "tactic_failed",
    "rewrite_failed",
    "simp_failed",
    "type_mismatch",
    "unsolved_goals",
    "elaboration_error",
    "timeout_or_heartbeat",
    "hole_present",
    "other",
)


@dataclass
class LeanMessage:
    line: int
    col: int
    severity: str
    text: str

    @property
    def category(self) -> str:
        return categorize_error(self.text)


@dataclass
class LeanResult:
    command: List[str]
    cwd: str
    file: str
    exit_code: int
    stdout: str
    stderr: str
    elapsed_seconds: float
    timed_out: bool = False
    messages: List[LeanMessage] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.exit_code == 0 and not self.timed_out and not self.errors

    @property
    def errors(self) -> List[LeanMessage]:
        return [m for m in self.messages if m.severity == "error"]

    def errors_in_lines(self, lo: int, hi: int) -> List[LeanMessage]:
        return [m for m in self.errors if lo <= m.line <= hi]

    def primary_category(self) -> Optional[str]:
        if self.timed_out:
            return "timeout_or_heartbeat"
        errs = self.errors
        if not errs:
            return None
        return errs[0].category

    def to_json(self) -> dict:
        d = asdict(self)
        d["ok"] = self.ok
        d["primary_category"] = self.primary_category()
        return d

    def save(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(self.to_json(), indent=1, ensure_ascii=False), encoding="utf-8")


def categorize_error(text: str) -> str:
    t = text.lower()
    if "sorry" in t and ("declaration uses" in t or "contains" in t):
        return "hole_present"
    if any(k in t for k in ("deterministic timeout", "maximum recursion depth", "heartbeats", "timed out")):
        return "timeout_or_heartbeat"
    if any(k in t for k in ("unknown identifier", "unknown constant", "unknown namespace", "unknown tactic")):
        return "unknown_constant_or_identifier"
    if "unsolved goals" in t:
        return "unsolved_goals"
    if any(k in t for k in ("motive is not type correct", "did not find instance of the pattern", "rewrite failed", "rw failed", "pattern is a metavariable")):
        return "rewrite_failed"
    if any(k in t for k in ("simp made no progress", "simp failed", "simp_all made no progress", "failed to simplify")):
        return "simp_failed"
    if any(k in t for k in ("type mismatch", "application type mismatch", "has type", "but is expected to have type")):
        return "type_mismatch"
    if any(k in t for k in ("failed", "tactic", "no goals", "not a proposition", "invalid alternative", "unfold failed")):
        return "tactic_failed"
    if any(k in t for k in ("failed to synthesize", "elaborat", "expected", "unexpected", "invalid", "ambiguous")):
        return "elaboration_error"
    return "other"


def parse_messages(output: str) -> List[LeanMessage]:
    msgs: List[LeanMessage] = []
    cur: Optional[LeanMessage] = None
    for line in output.splitlines():
        m = MSG_RE.match(line)
        if m:
            cur = LeanMessage(int(m.group("line")), int(m.group("col")), m.group("sev"), m.group("msg"))
            msgs.append(cur)
        elif cur is not None:
            cur.text += "\n" + line
    return msgs


class LeanRunner:
    def __init__(self, verina_root: Path, timeout: int = 300, elan_bin: Optional[Path] = None):
        self.verina_root = Path(verina_root).resolve()
        self.timeout = timeout
        self.elan_bin = Path(elan_bin) if elan_bin else Path.home() / ".elan" / "bin"
        if not (self.verina_root / "lakefile.lean").exists():
            raise FileNotFoundError(f"not a lake project: {self.verina_root}")

    def _env(self) -> dict:
        env = dict(os.environ)
        env["PATH"] = f"{self.elan_bin}{os.pathsep}{env.get('PATH', '')}"
        # keep Lean from spawning extra threads per process when we parallelize externally
        env.setdefault("LEAN_NUM_THREADS", "1")
        return env

    def compile(self, lean_file: Path, timeout: Optional[int] = None) -> LeanResult:
        lean_file = Path(lean_file).resolve()
        cmd = ["lake", "env", "lean", str(lean_file)]
        t0 = time.monotonic()
        timed_out = False
        try:
            proc = subprocess.run(
                cmd,
                cwd=str(self.verina_root),
                env=self._env(),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout or self.timeout,
                check=False,
            )
            out, err, code = proc.stdout.decode("utf-8", "replace"), proc.stderr.decode("utf-8", "replace"), proc.returncode
        except subprocess.TimeoutExpired as e:
            timed_out = True
            out = (e.stdout or b"").decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
            err = (e.stderr or b"").decode("utf-8", "replace") if isinstance(e.stderr, bytes) else (e.stderr or "")
            code = 124
        elapsed = time.monotonic() - t0
        msgs = parse_messages(out + "\n" + err)
        return LeanResult(
            command=cmd,
            cwd=str(self.verina_root),
            file=str(lean_file),
            exit_code=code,
            stdout=out,
            stderr=err,
            elapsed_seconds=round(elapsed, 3),
            timed_out=timed_out,
            messages=msgs,
        )

    def version_info(self) -> dict:
        env = self._env()
        def run(args):
            try:
                return subprocess.run(args, cwd=str(self.verina_root), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120).stdout.decode().strip()
            except Exception as e:  # pragma: no cover
                return f"ERROR: {e}"
        import hashlib
        manifest = self.verina_root / "lake-manifest.json"
        return {
            "lean_version": run(["lake", "env", "lean", "--version"]),
            "lake_version": run(["lake", "--version"]),
            "lean_toolchain_file": (self.verina_root / "lean-toolchain").read_text().strip(),
            "verina_commit": run(["git", "rev-parse", "HEAD"]),
            "lake_manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
        }


def contains_hole(text: str) -> bool:
    return re.search(r"(?<![\w'.])(sorry|admit)(?![\w'])", text) is not None
