"""Invariants A (spec unchanged), B (proof unchanged), F (same public header) and D (no certificate leak)
hold for every generated variant, checked without Lean."""

import os
from pathlib import Path

import pytest

from refactorproof.survival import apply_variant, block_line_range, same_public_header
from refactorproof.transformations import get_transformations
from refactorproof.verina_parser import iter_task_dirs, load_task

VERINA_ROOT = Path(os.environ.get("VERINA_ROOT", Path(__file__).resolve().parents[1] / "external" / "verina"))
pytestmark = pytest.mark.skipif(not (VERINA_ROOT / "datasets" / "verina").exists(), reason="VERINA not present")
TASK_DIRS = iter_task_dirs(VERINA_ROOT) if (VERINA_ROOT / "datasets" / "verina").exists() else []
TRANSFORMATIONS = get_transformations(["T1", "T2", "T3", "T4"])


@pytest.mark.parametrize("task_dir", TASK_DIRS, ids=[d.name for d in TASK_DIRS])
def test_variants_preserve_spec_proof_and_header(task_dir):
    tb = load_task(task_dir)
    for t in TRANSFORMATIONS:
        ok, reason = t.applicable(tb)
        variants = t.generate(tb, seed=0)
        if not ok:
            assert variants == [] and reason
            continue
        assert len(variants) >= 1
        for v in variants:
            new = apply_variant(tb, v)
            assert new.spec_hash() == tb.spec_hash()
            assert new.proof_hash() == tb.proof_hash()
            assert same_public_header(new, tb)  # Invariant F
            assert new.content("import") == tb.content("import")
            assert new.content("postcond") == tb.content("postcond")
            src = new.render()
            assert "rp_equiv" not in src and "RPOrig" not in src and "RPRef" not in src  # Invariant D
            assert "sorry" not in v.transformed_code and "admit" not in v.transformed_code
            # block replacement changed only code/code_aux
            for k, blk in tb.blocks.items():
                if k not in ("code", "code_aux"):
                    assert new.blocks[k] == blk
            # variant must differ from original in the code region
            assert v.transformed_code != tb.content("code") or v.transformed_code_aux != tb.content("code_aux")


def test_determinism():
    tb = load_task(TASK_DIRS[0])
    for t in TRANSFORMATIONS:
        a = t.generate(tb, seed=0)
        b = t.generate(tb, seed=0)
        assert [x.to_json() for x in a] == [x.to_json() for x in b]


def test_proof_line_range_points_at_proof():
    tb = load_task(VERINA_ROOT / "datasets" / "verina" / "verina_basic_15")
    lo, hi = block_line_range(tb, "proof")
    lines = tb.render().splitlines()
    assert "@start proof" in lines[lo - 2]
    assert "@end proof" in lines[hi - 1]
