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
  let __rp_tmp_1171a237 : Int :=
    let y := x * 2
    y + x
  __rp_tmp_1171a237
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
  have h₁ : ((x * 2) + x) / 3 = x := by
    have h₁₁ : (x * 2 + x : ℤ) = 3 * x := by
      ring
    rw [h₁₁]
    have h₁₂ : (3 * x : ℤ) / 3 = x := by
      have h₁₃ : (3 : ℤ) ≠ 0 := by norm_num
      have h₁₄ : (3 * x : ℤ) / 3 = x := by
        apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
        <;> ring
        <;> norm_num
        <;> linarith
      exact h₁₄
    exact h₁₂

  have h₂ : ((x * 2) + x) / 3 * 3 = (x * 2) + x := by
    have h₂₁ : ((x * 2) + x : ℤ) = 3 * x := by
      ring
    rw [h₁]
    <;> ring_nf
    <;> omega

  have h₃ : Triple_postcond x (Triple x h_precond) h_precond := by
    dsimp [Triple, Triple_postcond, Triple_precond] at *
    <;> simp_all [Int.mul_ediv_cancel_left]
    <;> ring_nf at *
    <;> omega

  exact h₃
  -- !benchmark @end proof
