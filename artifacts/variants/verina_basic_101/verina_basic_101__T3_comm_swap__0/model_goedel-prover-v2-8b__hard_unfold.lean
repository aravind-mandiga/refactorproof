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
  unfold Triple Triple_postcond
  have h₁ : ((x * 2 + x : ℤ) / 3 : ℤ) = x := by
    have h₁₁ : (x * 2 + x : ℤ) = x * 3 := by ring
    rw [h₁₁]
    have h₁₂ : (x * 3 : ℤ) / 3 = x := by
      have h₁₃ : (x * 3 : ℤ) = 3 * x := by ring
      rw [h₁₃]
      have h₁₄ : (3 : ℤ) * x / 3 = x := by
        have h₁₅ : (3 : ℤ) * x / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (show (3 : ℤ) ≠ 0 by norm_num)
          <;> ring_nf
          <;> linarith
        exact h₁₅
      exact h₁₄
    exact h₁₂

  have h₂ : ((x * 2 + x : ℤ) / 3 : ℤ) * 3 = x * 2 + x := by
    have h₂₁ : (x * 2 + x : ℤ) = x * 3 := by ring
    rw [h₂₁]
    have h₂₂ : (x * 3 : ℤ) / 3 * 3 = x * 3 := by
      have h₂₃ : (x * 3 : ℤ) / 3 * 3 = x * 3 := by
        have h₂₄ : (x * 3 : ℤ) % 3 = 0 := by
          -- Prove that (x * 3) % 3 = 0
          omega
        have h₂₅ : (x * 3 : ℤ) / 3 * 3 = x * 3 := by
          -- Use the fact that (x * 3) % 3 = 0 to simplify the division
          have h₂₆ : (x * 3 : ℤ) = 3 * ((x * 3 : ℤ) / 3) + (x * 3 : ℤ) % 3 := by
            omega
          rw [h₂₄] at h₂₆
          ring_nf at h₂₆ ⊢
          <;> omega
        exact h₂₅
      exact h₂₃
    linarith

  simp_all [Triple, Triple_postcond, Triple_precond, Int.mul_emod, Int.add_emod]
  <;>
  (try omega) <;>
  (try ring_nf at *) <;>
  (try norm_num) <;>
  (try omega)
  -- !benchmark @end proof
