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
  have h_main : (x * 3 : Int) / 3 = x := by
    have h₁ : (x * 3 : Int) / 3 = x := by
      have h₂ : (x * 3 : Int) = 3 * x := by ring
      rw [h₂]
      -- Use the fact that (3 * x) / 3 = x for any integer x
      have h₃ : (3 : Int) ≠ 0 := by norm_num
      have h₄ : (3 * x : Int) / 3 = x := by
        -- Prove that (3 * x) / 3 = x using the properties of integer division
        have h₅ : (3 * x : Int) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
          <;> ring
          <;> norm_num
        exact h₅
      exact h₄
    exact h₁

  have h_final : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    dsimp [Triple_postcond, Triple] at *
    constructor
    · -- Prove that (x * 3) / 3 = x
      exact h_main
    · -- Prove that ((x * 3) / 3) * 3 = x * 3
      have h₁ : (x * 3 : Int) / 3 = x := h_main
      have h₂ : ((x * 3 : Int) / 3) * 3 = x * 3 := by
        rw [h₁]
        <;> ring
      exact h₂

  exact h_final
  -- !benchmark @end proof
