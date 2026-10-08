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
  have h1 : Triple (x) h_precond = x * 3 := by
    rfl
    <;> simp [Triple, Triple_precond]
    <;> ring
    <;> simp_all
    <;> linarith

  have h2 : (x * 3 : ℤ) / 3 = x := by
    have h₂ : (x * 3 : ℤ) = 3 * x := by ring
    rw [h₂]
    -- Use the property of integer division to simplify the expression
    have h₃ : (3 * x : ℤ) / 3 = x := by
      -- Use the fact that 3 * x is divisible by 3
      have h₄ : (3 : ℤ) ≠ 0 := by norm_num
      -- Use the division algorithm to simplify the expression
      rw [Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]
      <;> ring
      <;> simp_all
      <;> linarith
    exact h₃

  have h3 : (x * 3 : ℤ) / 3 * 3 = x * 3 := by
    have h₃ : (x * 3 : ℤ) / 3 = x := h2
    rw [h₃]
    <;> ring
    <;> simp_all
    <;> linarith

  have h4 : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    rw [h1]
    constructor
    · -- Prove the first part of the conjunction: (x * 3 : ℤ) / 3 = x
      exact h2
    · -- Prove the second part of the conjunction: (x * 3 : ℤ) / 3 * 3 = x * 3
      exact h3

  exact h4
  -- !benchmark @end proof
