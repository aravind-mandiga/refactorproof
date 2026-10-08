-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  -- !benchmark @start code
  (b + a) / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  -- !benchmark @start postcond
  2 * result = a + b - ((a + b) % 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2) := by
    have h₁ : (a + b : ℤ) = 2 * ((a + b) / 2) + ((a + b) % 2) := by
      have h₂ : (a + b : ℤ) = 2 * ((a + b) / 2) + ((a + b) % 2) := by
        -- Use the property of integer division and modulo to express `a + b` in terms of `(a + b) / 2` and `(a + b) % 2`
        have h₃ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
          -- Prove that `(a + b) % 2` is either 0 or 1
          have h₄ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
            have h₅ : (a + b : ℤ) % 2 = 0 ∨ (a + b : ℤ) % 2 = 1 := by
              omega
            exact h₅
          exact h₄
        -- Consider the two cases for `(a + b) % 2`
        rcases h₃ with (h₃ | h₃)
        · -- Case 1: `(a + b) % 2 = 0`
          have h₄ : (a + b : ℤ) = 2 * ((a + b) / 2) + ((a + b) % 2) := by
            have h₅ : (a + b : ℤ) = 2 * ((a + b) / 2) := by
              omega
            omega
          exact h₄
        · -- Case 2: `(a + b) % 2 = 1`
          have h₄ : (a + b : ℤ) = 2 * ((a + b) / 2) + ((a + b) % 2) := by
            have h₅ : (a + b : ℤ) = 2 * ((a + b) / 2) + 1 := by
              omega
            omega
          exact h₄
      exact h₂
    -- Use the above result to prove the main statement
    have h₂ : 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2) := by
      omega
    exact h₂

  have h₁ : ComputeAvg (a) (b) h_precond = (a + b) / 2 := by
    rfl

  have h₂ : 2 * (ComputeAvg (a) (b) h_precond) = (a + b) - ((a + b) % 2) := by
    rw [h₁]
    <;> simpa using h_main

  have h₃ : ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
    rw [ComputeAvg_postcond]
    <;> simpa [h₁] using h₂

  exact h₃
  -- !benchmark @end proof
