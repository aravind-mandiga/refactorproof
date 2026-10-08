"""Byte-perfect round-trip of the marker parser over the entire VERINA dataset."""

import os
from pathlib import Path

import pytest

from refactorproof.verina_parser import (
    REQUIRED_BLOCKS,
    iter_task_dirs,
    load_task,
    parse_source,
)

VERINA_ROOT = Path(os.environ.get("VERINA_ROOT", Path(__file__).resolve().parents[1] / "external" / "verina"))

pytestmark = pytest.mark.skipif(not (VERINA_ROOT / "datasets" / "verina").exists(), reason="VERINA not present")

TASK_DIRS = iter_task_dirs(VERINA_ROOT) if (VERINA_ROOT / "datasets" / "verina").exists() else []


def test_dataset_has_189_tasks():
    assert len(TASK_DIRS) == 189


@pytest.mark.parametrize("task_dir", TASK_DIRS, ids=[d.name for d in TASK_DIRS])
def test_roundtrip_bytes(task_dir):
    raw = (task_dir / "task.lean").read_bytes()
    tb = load_task(task_dir)
    assert tb.render().encode("utf-8") == raw


@pytest.mark.parametrize("task_dir", TASK_DIRS, ids=[d.name for d in TASK_DIRS])
def test_required_blocks_and_header(task_dir):
    tb = load_task(task_dir)
    for b in REQUIRED_BLOCKS:
        assert tb.has_block(b), b
    assert tb.def_header_name() == tb.signature.name


@pytest.mark.parametrize("task_dir", TASK_DIRS, ids=[d.name for d in TASK_DIRS])
def test_block_replacement_is_local(task_dir):
    tb = load_task(task_dir)
    new = tb.with_block_content("code", "  0\n")
    assert new.spec_hash() == tb.spec_hash()
    assert new.proof_hash() == tb.proof_hash()
    assert new.content("code") == "  0\n"
    # every other block unchanged
    for k, blk in tb.blocks.items():
        if k != "code":
            assert new.blocks[k] == blk


def test_marker_token_boundaries():
    src = (
        "-- !benchmark @start code_aux\nA\n-- !benchmark @end code_aux\n"
        "def f : Nat :=\n  -- !benchmark @start code\n  1\n  -- !benchmark @end code\n"
    )
    segs = parse_source(src)
    names = [s.name for s in segs if not isinstance(s, str)]
    assert names == ["code_aux", "code"]
    assert "".join(s if isinstance(s, str) else s.render() for s in segs) == src
