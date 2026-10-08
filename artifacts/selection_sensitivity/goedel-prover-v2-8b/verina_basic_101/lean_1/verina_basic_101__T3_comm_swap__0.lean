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
  let y := 2 * x
  y + x
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
  have h_result_def : Triple (x) h_precond = x * 3 := by
    dsimp [Triple, h_precond]
    <;> ring
    <;> simp_all
    <;> omega

  have h_div : (Triple (x) h_precond) / 3 = x := by
    rw [h_result_def]
    have h₁ : (x * 3 : ℤ) / 3 = x := by
      have h₂ : (x * 3 : ℤ) / 3 = x := by
        have h₃ : (x * 3 : ℤ) = 3 * x := by ring
        rw [h₃]
        have h₄ : (3 * x : ℤ) / 3 = x := by
          have h₅ : (3 : ℤ) ≠ 0 := by norm_num
          have h₆ : (3 * x : ℤ) / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            <;> ring
            <;> omega
          exact h₆
        exact h₄
      exact h₂
    exact h₁

  have h_mul : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    rw [h_div]
    have h₁ : (x * 3 : ℤ) = Triple (x) h_precond := by
      rw [h_result_def]
      <;> ring
    linarith

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: (Triple (x) h_precond) / 3 = x
      exact h_div
    · -- Prove the second part of the conjunction: ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond
      exact h_mul

  exact h_main
  -- !benchmark @end proof
