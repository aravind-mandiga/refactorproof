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

private def Triple__rp_helper_c4a61f58 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  x * 3
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_c4a61f58 x h_precond
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
  have h1 : (Triple (x) h_precond) / 3 = x := by
    have h₁ : Triple (x) h_precond = x * 3 := by
      simp [Triple, Triple__rp_helper_c4a61f58]
      <;> ring_nf
      <;> omega
    rw [h₁]
    -- Now we need to prove that (x * 3) / 3 = x
    have h₂ : (x * 3) / 3 = x := by
      -- Use the property of integer division to show that (x * 3) / 3 = x
      have h₃ : x * 3 / 3 = x := by
        -- Use the fact that 3 is a non-zero integer to simplify the division
        have h₄ : x * 3 / 3 = x := by
          -- Use the property of integer division to show that (x * 3) / 3 = x
          omega
        exact h₄
      exact h₃
    exact h₂

  have h2 : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₂ : Triple (x) h_precond = x * 3 := by
      simp [Triple]
      <;> ring_nf
      <;> omega
    rw [h₂] at *
    have h₃ : ((x * 3) / 3) * 3 = x * 3 := by
      have h₄ : (x * 3) / 3 = x := by
        have h₅ : x * 3 / 3 = x := by
          omega
        exact h₅
      rw [h₄]
      <;> ring_nf
      <;> omega
    simpa [h₂] using h₃

  have h3 : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the postcondition: (Triple (x) h_precond) / 3 = x
      exact h1
    · -- Prove the second part of the postcondition: ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond
      exact h2

  exact h3
  -- !benchmark @end proof
