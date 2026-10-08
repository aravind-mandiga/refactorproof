from refactorproof.transformations.helper_extract import parse_header
from refactorproof.transformations import get_transformations
from refactorproof.verina_parser import Signature, parse_task_source

SRC = """-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def foo_precond (x : Nat) (y : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond

-- !benchmark @start code_aux

-- !benchmark @end code_aux

def foo (x : Nat) (y : Nat) (h_precond : foo_precond (x) (y)) : Nat :=
  -- !benchmark @start code
  if x < y then
    y
  else
    x + 1
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux

@[reducible, simp]
def foo_postcond (x : Nat) (y : Nat) (result: Nat) (h_precond : foo_precond (x) (y)) :=
  -- !benchmark @start postcond
  result ≥ x
  -- !benchmark @end postcond

-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

theorem foo_spec_satisfied (x: Nat) (y: Nat) (h_precond : foo_precond (x) (y)) :
    foo_postcond (x) (y) (foo (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold foo foo_postcond
  split <;> omega
  -- !benchmark @end proof
"""


def _task():
    sig = Signature(name="foo", parameters=[{"param_name": "x", "param_type": "Nat"}, {"param_name": "y", "param_type": "Nat"}], return_type="Nat")
    return parse_task_source(SRC, "toy", sig)


def test_parse_header():
    name, binders, attrs, mods = parse_header("def foo (x : Nat) (y : Nat) (h_precond : foo_precond (x) (y)) : Nat :=")
    assert name == "foo" and binders == ["x", "y", "h_precond"]
    assert parse_header("def foo {α : Type} (x : α) : α :=") is None
    assert parse_header("def foo [inst : BEq α] (x : α) : α :=") is None


def test_let_intro_shape():
    (t,) = get_transformations(["T1"])
    tb = _task()
    (v,) = t.generate(tb, 0)
    lines = v.transformed_code.splitlines()
    assert lines[0].startswith("  let __rp_tmp_")
    assert lines[-1].strip().startswith("__rp_tmp_")
    assert lines[1] == "    if x < y then"
    assert v.transformed_code_aux == tb.content("code_aux")
    assert v.severity == "D"


def test_helper_extract_shape():
    (t,) = get_transformations(["T2"])
    tb = _task()
    (v,) = t.generate(tb, 0)
    helper = v.helper_names[0]
    assert v.transformed_code == f"  {helper} x y h_precond\n"
    assert f"private def {helper} (x : Nat) (y : Nat) (h_precond : foo_precond (x) (y)) : Nat :=" in v.transformed_code_aux
    assert "  if x < y then" in v.transformed_code_aux
    assert v.severity == "S"


def test_helper_extract_skips_recursive():
    (t,) = get_transformations(["T2"])
    src = SRC.replace("    x + 1\n", "    foo x 0 h_precond\n")
    sig = Signature(name="foo", parameters=[], return_type="Nat")
    tb = parse_task_source(src, "toy", sig)
    ok, reason = t.applicable(tb)
    assert not ok and reason == "self_recursive_body"
