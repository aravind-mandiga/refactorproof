"""Structural checks on certificate construction and the evaluation-file/certificate separation (no Lean)."""

import os
from pathlib import Path

import pytest

from refactorproof.certify import build_certificate_source, header_parts, judge
from refactorproof.lean_runner import LeanMessage, LeanResult, contains_hole
from refactorproof.survival import apply_variant
from refactorproof.transformations import get_transformations
from refactorproof.verina_parser import iter_task_dirs, load_task

VERINA_ROOT = Path(os.environ.get("VERINA_ROOT", Path(__file__).resolve().parents[1] / "external" / "verina"))
pytestmark = pytest.mark.skipif(not (VERINA_ROOT / "datasets" / "verina").exists(), reason="VERINA not present")
TASK_DIRS = iter_task_dirs(VERINA_ROOT) if (VERINA_ROOT / "datasets" / "verina").exists() else []
TRANSFORMATIONS = get_transformations(["T1", "T2", "T3", "T4"])


@pytest.mark.parametrize("task_dir", TASK_DIRS, ids=[d.name for d in TASK_DIRS])
def test_certificate_source_structure(task_dir):
    tb = load_task(task_dir)
    binders, args, ret = header_parts(tb)
    assert args.split(), "header must have explicit binders"
    for t in TRANSFORMATIONS:
        for v in t.generate(tb, 0):
            src, regions, theorems = build_certificate_source(tb, v)
            assert "namespace RPOrig" in src and "namespace RPRef" in src
            assert not contains_hole(src)
            # no new axioms beyond those the upstream task itself declares (two VERINA tasks axiomatise Float facts)
            assert src.count("axiom ") == tb.render().count("axiom ")
            assert {"rfl", "rfl_nosmart", "delta_rfl", "simp_only", "simp"} <= set(theorems)
            assert regions["prefix"][0] == 1 and regions["orig"][0] > regions["prefix"][1] and regions["ref"][0] > regions["orig"][1]
            assert all(theorems[k][0] > regions["ref"][1] for k in theorems)
            # the original body appears verbatim inside RPOrig, the transformed inside RPRef
            assert tb.content("code").strip() in src
            assert v.transformed_code.strip() in src
            # certificate laws reach the simp set
            for law in v.certificate_laws:
                assert law in src
            # and the survival file never contains the certificate
            ev = apply_variant(tb, v).render()
            assert "rp_equiv" not in ev and "RPOrig" not in ev and "RPRef" not in ev


def _res(errors):
    return LeanResult(command=[], cwd="", file="", exit_code=1 if errors else 0, stdout="", stderr="", elapsed_seconds=0.1, messages=[LeanMessage(l, 0, "error", m) for l, m in errors])


def test_judge_attributes_errors_to_theorems():
    regions = {"prefix": (1, 10), "orig": (11, 20), "ref": (21, 30)}
    theorems = {"rfl": (33, 35), "rfl_nosmart": (44, 46), "delta_rfl": (47, 50), "simp_only": (36, 39), "simp": (40, 43)}
    # rfl fails, simp only succeeds
    j = judge(_res([(35, "The rfl tactic failed"), (46, "type mismatch"), (49, "unknown constant")]), regions, theorems)
    assert j["certificate_valid"] and not j["certificate_closed_by_rfl"] and j["certificate_level"] == "simp_only"
    # nosmart rfl succeeds -> still a definitional certificate
    j = judge(_res([(35, "type mismatch")]), regions, theorems)
    assert j["certificate_valid"] and j["certificate_closed_by_rfl"] and j["rfl_level"] == "rfl_nosmart" and not j["certificate_closed_by_plain_rfl"]
    # everything passes
    j = judge(_res([]), regions, theorems)
    assert j["certificate_valid"] and j["certificate_closed_by_rfl"] and j["certificate_level"] == "rfl"
    # transformed definition does not elaborate -> not certified even if theorems have no errors
    j = judge(_res([(25, "unknown identifier 'foo'")]), regions, theorems)
    assert not j["certificate_valid"] and j["certificate_failure_category"] == "variant_does_not_elaborate"
    # all theorems fail
    j = judge(_res([(35, "rfl failed"), (46, "type mismatch"), (49, "type mismatch"), (38, "simp made no progress"), (42, "unsolved goals")]), regions, theorems)
    assert not j["certificate_valid"] and j["certificate_level"] is None
