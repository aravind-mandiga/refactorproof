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

private def Triple__rp_helper_65b561a3 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := x * 2
  y + x
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_65b561a3 x h_precond
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
  have h_main : Triple (x) h_precond = 3 * x := by
    simp [Triple, Int.mul_add, Int.add_mul, Int.mul_one, Int.mul_assoc]
    <;> ring
    <;> omega

  have h_first : (Triple (x) h_precond) / 3 = x := by
    rw [h_main]
    have h : (3 * x : ℤ) / 3 = x := by
      have h₁ : (3 * x : ℤ) / 3 = x := by
        have h₂ : (3 * x : ℤ) / 3 = x := by
          omega
        exact h₂
      exact h₁
    exact h

  have h_second : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    rw [h_main]
    have h : (3 * x : ℤ) / 3 * 3 = 3 * x := by
      have h₁ : (3 * x : ℤ) / 3 = x := by
        have h₂ : (3 * x : ℤ) / 3 = x := by
          omega
        exact h₂
      rw [h₁]
      <;> ring
      <;> omega
    exact h

  have h_final : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    simp only [Triple_postcond] at *
    constructor
    · -- Prove the first condition: (Triple (x) h_precond) / 3 = x
      simpa [h_main, h_first, h_second] using h_first
    · -- Prove the second condition: (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond
      simpa [h_main, h_first, h_second] using h_second
  exact h_final
  -- !benchmark @end proof
