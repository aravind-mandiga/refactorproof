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
  3 * x
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
      -- Use the property of integer division to simplify the expression
      have h₂ : x * 3 = 3 * x := by ring
      rw [h₂]
      -- Use the fact that 3 * x / 3 = x for any integer x
      have h₃ : (3 : Int) ≠ 0 := by norm_num
      have h₄ : (3 * x : Int) / 3 = x := by
        -- Use the property of integer division to simplify the expression
        have h₅ : (3 * x : Int) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
          <;> ring_nf <;> norm_num <;> linarith
        exact h₅
      exact h₄
    exact h₁

  have h_final : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    have h₁ : Triple (x) h_precond = x * 3 := by
      simp [Triple]
      <;>
      aesop
    have h₂ : (Triple (x) h_precond : Int) / 3 = x := by
      rw [h₁]
      <;>
      simpa using h_main
    have h₃ : (Triple (x) h_precond : Int) / 3 * 3 = Triple (x) h_precond := by
      rw [h₁]
      have h₄ : (x * 3 : Int) / 3 = x := h_main
      have h₅ : (x * 3 : Int) / 3 * 3 = x * 3 := by
        calc
          (x * 3 : Int) / 3 * 3 = x * 3 := by
            have h₆ : (x * 3 : Int) / 3 = x := h_main
            rw [h₆]
            <;> ring
          _ = x * 3 := by rfl
      simpa [h₁] using h₅
    simp_all [Triple_postcond]
    <;>
    aesop

  exact h_final
  -- !benchmark @end proof
