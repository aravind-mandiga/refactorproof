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
  have h_main : (x ≥ 0 → x = (if x < 0 then -x else x)) ∧ (x < 0 → x + (if x < 0 then -x else x) = 0) := by
    constructor
    · -- Prove (x ≥ 0 → x = (if x < 0 then -x else x))
      intro hx
      -- Case: x ≥ 0
      have h₁ : ¬x < 0 := by linarith
      have h₂ : (if x < 0 then -x else x) = x := by
        split_ifs <;> simp_all
        <;> linarith
      rw [h₂]
    · -- Prove (x < 0 → x + (if x < 0 then -x else x) = 0)
      intro hx
      -- Case: x < 0
      have h₁ : x < 0 := hx
      have h₂ : (if x < 0 then -x else x) = -x := by
        split_ifs <;> simp_all
        <;> linarith
      rw [h₂]
      -- Simplify x + (-x) = 0
      have h₃ : x + (-x) = 0 := by ring
      exact h₃

  have h₁ : (x ≥ 0 → x = (Abs x h_precond)) ∧ (x < 0 → x + (Abs x h_precond) = 0) := by
    have h₂ : Abs x h_precond = (if x < 0 then -x else x) := by
      simp [Abs]
      <;>
      simp_all [Abs_precond]
      <;>
      aesop
    constructor
    · -- Prove (x ≥ 0 → x = (Abs x h_precond))
      intro hx
      have h₃ : x = (if x < 0 then -x else x) := (h_main.1 hx)
      rw [h₂] at *
      exact h₃
    · -- Prove (x < 0 → x + (Abs x h_precond) = 0)
      intro hx
      have h₃ : x + (if x < 0 then -x else x) = 0 := (h_main.2 hx)
      rw [h₂] at *
      exact h₃

  have h₂ : Abs_postcond x (Abs x h_precond) h_precond := by
    simp only [Abs_postcond]
    exact h₁

  exact h₂
  -- !benchmark @end proof
