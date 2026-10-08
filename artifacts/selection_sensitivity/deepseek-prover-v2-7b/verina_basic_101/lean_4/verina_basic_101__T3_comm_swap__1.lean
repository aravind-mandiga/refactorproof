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
  let y := x * 2
  x + y
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
  have h_result : Triple (x) h_precond = 3 * x := by
    simp [Triple, Triple_precond]
    <;> ring_nf
    <;> omega

  have h_div : (Triple (x) h_precond) / 3 = x := by
    rw [h_result]
    -- We need to show that (3 * x) / 3 = x for any integer x.
    have h₁ : (3 * x) / 3 = x := by
      have h₂ : x * 3 = 3 * x := by ring
      -- Using the property of integer division, we know that (3 * x) / 3 = x.
      omega
    omega

  have h_mul : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    rw [h_result]
    have h : x * 3 = 3 * x := by ring
    -- Simplify the goal using the property of integer division
    have h₁ : ((3 * x) / 3) * 3 = (3 * x) := by
      have h₂ : (3 * x) / 3 * 3 = (3 * x) := by
        -- Use the property that a number divided by its divisor multiplied by the divisor gives back the original number
        have h₃ : (3 * x) % 3 = 0 := by
          have : (3 * x) % 3 = 0 := by
            omega
          exact this
        omega
      exact h₂
    omega

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    have h₁ : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
      constructor
      · -- Prove the first part of the conjunction: (result / 3) = x
        exact h_div
      · -- Prove the second part of the conjunction: ((result / 3) * 3) = result
        exact h_mul
    exact h₁

  exact h_main
  -- !benchmark @end proof
