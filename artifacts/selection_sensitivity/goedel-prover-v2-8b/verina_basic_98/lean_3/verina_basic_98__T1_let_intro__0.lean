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
  let __rp_tmp_d53b48dc : Int :=
    x * 3
  __rp_tmp_d53b48dc
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
  have h₁ : (Triple (x) h_precond : ℤ) = x * 3 := by
    simp [Triple]
    <;> ring_nf
    <;> simp_all [Triple_precond]
    <;> norm_num
    <;> linarith

  have h₂ : (x * 3 : ℤ) / 3 = x := by
    have h₂₁ : (x * 3 : ℤ) / 3 = x := by
      have h₂₂ : x * 3 = 3 * x := by ring
      rw [h₂₂]
      have h₂₃ : (3 : ℤ) * x / 3 = x := by
        have h₂₄ : (3 : ℤ) ≠ 0 := by norm_num
        have h₂₅ : (3 : ℤ) * x / 3 = x := by
          rw [Int.mul_ediv_cancel_left _ (by norm_num : (3 : ℤ) ≠ 0)]
        exact h₂₅
      exact h₂₃
    exact h₂₁

  have h₃ : (x * 3 : ℤ) / 3 * 3 = x * 3 := by
    have h₃₁ : (x * 3 : ℤ) / 3 * 3 = x * 3 := by
      have h₃₂ : (x * 3 : ℤ) / 3 = x := h₂
      rw [h₃₂]
      <;> ring
    exact h₃₁

  have h₄ : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    simp_all [Triple_postcond, Triple, Int.emod_eq_of_lt]
    <;> omega

  exact h₄
  -- !benchmark @end proof
