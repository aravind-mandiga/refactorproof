-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  3 * x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result / 3 = x ∧ result / 3 * 3 = result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : (x * 3 : ℤ) / 3 = x := by
    have h₁₁ : (x * 3 : ℤ) / 3 = x := by
      have h₁₂ : (x * 3 : ℤ) / 3 = x := by
        -- Use the property of integer division to simplify the expression
        have h₁₃ : (x * 3 : ℤ) / 3 = x := by
          -- Prove that (x * 3) / 3 = x using the properties of integer division
          have h₁₄ : (x * 3 : ℤ) / 3 = x := by
            -- Use the fact that x * 3 is a multiple of 3
            have h₁₅ : (x * 3 : ℤ) / 3 = x := by
              -- Use the property of integer division to simplify the expression
              omega
            exact h₁₅
          exact h₁₄
        exact h₁₃
      exact h₁₂
    exact h₁₁

  have h₂ : ((x * 3 : ℤ) / 3) * 3 = x * 3 := by
    rw [h₁]
    <;> ring
    <;> omega

  have h₃ : Triple_postcond x (Triple x h_precond) h_precond := by
    have h₄ : Triple x h_precond = x * 3 := by
      simp [Triple]
    rw [h₄]
    constructor
    · -- Prove the first condition: (x * 3) / 3 = x
      exact h₁
    · -- Prove the second condition: ((x * 3) / 3) * 3 = x * 3
      exact h₂

  exact h₃
  -- !benchmark @end proof
