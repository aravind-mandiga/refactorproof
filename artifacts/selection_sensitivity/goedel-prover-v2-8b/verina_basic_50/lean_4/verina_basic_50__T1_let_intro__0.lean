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

-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  let __rp_tmp_84978ba1 : Int :=
    if x < 0 then -x else x
  __rp_tmp_84978ba1
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
  have h_main : (x ≥ 0 → x = (Abs (x) h_precond)) ∧ (x < 0 → x + (Abs (x) h_precond) = 0) := by
    constructor
    · -- Prove the first part: x ≥ 0 → x = Abs (x) h_precond
      intro hx
      have h₁ : Abs (x) h_precond = x := by
        -- Since x ≥ 0, we use the else branch of the if statement in Abs
        have h₂ : ¬(x < 0) := by linarith
        have h₃ : Abs (x) h_precond = x := by
          simp [Abs, h₂, h_precond]
        exact h₃
      -- Substitute the result back into the goal
      rw [h₁]
    · -- Prove the second part: x < 0 → x + Abs (x) h_precond = 0
      intro hx
      have h₁ : Abs (x) h_precond = -x := by
        -- Since x < 0, we use the first branch of the if statement in Abs
        have h₂ : x < 0 := hx
        have h₃ : Abs (x) h_precond = -x := by
          simp [Abs, h₂, h_precond]
        exact h₃
      -- Substitute the result back into the goal
      rw [h₁]
      linarith
  exact h_main
  -- !benchmark @end proof
