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
  if ¬ (x < 0) then x
  else -x
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
  have h_main : (x ≥ 0 → x = (if x < 0 then -x else x)) ∧ (x < 0 → x + (if x < 0 then -x else x) = 0) := by
    constructor
    · -- Prove the first part: x ≥ 0 → x = (if x < 0 then -x else x)
      intro hx
      have h₁ : ¬(x < 0) := by linarith
      have h₂ : (if x < 0 then -x else x) = x := by
        split_ifs <;> simp_all
        <;> linarith
      linarith
    · -- Prove the second part: x < 0 → x + (if x < 0 then -x else x) = 0
      intro hx
      have h₁ : (if x < 0 then -x else x) = -x := by
        split_ifs <;> simp_all
        <;> linarith
      have h₂ : x + (if x < 0 then -x else x) = 0 := by
        rw [h₁]
        linarith
      exact h₂

  -- Use the main result to prove the postcondition
  simp only [Abs_postcond, Abs] at *
  tauto
  -- !benchmark @end proof
