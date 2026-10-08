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

private def Abs__rp_branch_c6672445 (x : Int) (h_precond : Abs_precond (x)) : Int :=
  x
-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  if x < 0 then -x else
    Abs__rp_branch_c6672445 x h_precond
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
  unfold Abs Abs_postcond
  have h_main₁ : (x ≥ 0 → x = Abs x h_precond) := by
    intro h
    have h₁ : Abs x h_precond = x := by
      simp [Abs, h_precond, h]
      <;> aesop
    linarith

  have h_main₂ : (x < 0 → x + Abs x h_precond = 0) := by
    intro h
    have h₁ : Abs x h_precond = -x := by
      simp [Abs, h_precond, h]
      <;> aesop
    rw [h₁]
    <;> linarith

  have h_main : Abs_postcond (x) (Abs (x) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: x ≥ 0 → x = |x|
      intro hx
      have h₁ : x = Abs x h_precond := by
        have h₂ : x ≥ 0 := hx
        have h₃ : Abs x h_precond = x := by
          -- Since x ≥ 0, |x| = x
          simp [Abs, h_precond, h₂]
          <;> aesop
        linarith
      exact h₁
    · -- Prove the second part of the conjunction: x < 0 → x + |x| = 0
      intro hx
      have h₁ : x + Abs x h_precond = 0 := by
        have h₂ : x < 0 := hx
        have h₃ : Abs x h_precond = -x := by
          -- Since x < 0, |x| = -x
          simp [Abs, h_precond, h₂]
          <;> aesop
        rw [h₃]
        linarith
      exact h₁

  exact h_main
  -- !benchmark @end proof
