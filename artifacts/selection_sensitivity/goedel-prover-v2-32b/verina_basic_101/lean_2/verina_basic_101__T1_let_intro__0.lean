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
  have h_result : Triple (x) h_precond = 3 * x := by
    dsimp [Triple]
    ring_nf
    <;> simp_all [Triple_precond]
    <;> norm_num
    <;> linarith

  have h_div : (3 * x : Int) / 3 = x := by
    have h₁ : (3 : Int) ≠ 0 := by norm_num
    have h₂ : (3 * x : Int) / 3 = x := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
      <;> ring_nf
      <;> norm_num
      <;> linarith
    exact h₂

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    have h₁ : (Triple (x) h_precond) / 3 = x := by
      rw [h_result]
      -- Now we need to prove that (3 * x) / 3 = x
      have h₂ : (3 * x : Int) / 3 = x := h_div
      exact h₂
    have h₂ : (Triple (x) h_precond) / 3 * 3 = (Triple (x) h_precond) := by
      rw [h_result]
      -- Now we need to prove that ((3 * x) / 3) * 3 = 3 * x
      have h₃ : (3 * x : Int) / 3 = x := h_div
      have h₄ : ((3 * x : Int) / 3) * 3 = (3 * x : Int) := by
        rw [h₃]
        <;> ring_nf
        <;> norm_num
        <;> linarith
      exact h₄
    -- Combine the two results to get the final postcondition
    exact ⟨h₁, h₂⟩

  exact h_main
  -- !benchmark @end proof
