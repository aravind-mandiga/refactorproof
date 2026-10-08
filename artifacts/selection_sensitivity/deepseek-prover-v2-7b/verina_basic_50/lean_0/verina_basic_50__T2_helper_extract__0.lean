-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def Abs__rp_helper_4386b369 (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x
-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  Abs__rp_helper_4386b369 x h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  -- !benchmark @start postcond
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Abs_spec_satisfied (x: Int) (h_precond : Abs_precond (x)) :
    Abs_postcond (x) (Abs (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main₁ : x ≥ 0 → x = Abs (x) h_precond := by
    intro h
    have h₁ : Abs (x) h_precond = x := by
      simp [Abs, h_precond, h]
      <;> aesop
    rw [h₁]
    <;> simp_all
    <;> aesop

  have h_main₂ : x < 0 → x + Abs (x) h_precond = 0 := by
    intro h
    have h₁ : Abs (x) h_precond = -x := by
      simp [Abs, h_precond, h]
      <;> aesop
    rw [h₁]
    <;> linarith

  constructor
  · -- Prove the first part of the conjunction: x ≥ 0 → x = Abs (x) h_precond
    exact h_main₁
  · -- Prove the second part of the conjunction: x < 0 → x + Abs (x) h_precond = 0
    exact h_main₂
  -- !benchmark @end proof
