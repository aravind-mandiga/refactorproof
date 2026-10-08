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
  have h₁ : (Triple x h_precond) / 3 = x := by
    have h₂ : Triple x h_precond = x * 3 := by
      -- Expand the definition of `Triple`
      rfl
    rw [h₂]
    -- Use the property of integer division to simplify the expression
    have h₃ : (x * 3) / 3 = x := by
      -- Prove that (x * 3) / 3 = x using the property of integer division
      omega
    exact h₃

  have h₂ : ((Triple x h_precond) / 3) * 3 = Triple x h_precond := by
    have h₃ : Triple x h_precond = x * 3 := by
      rfl
    rw [h₃] at *
    have h₄ : ((x * 3) / 3) * 3 = x * 3 := by
      have h₅ : x * 3 / 3 = x := by
        -- Use the property of integer division to simplify the expression
        omega
      rw [h₅]
      <;> ring
    exact h₄

  have h₃ : Triple_postcond x (Triple x h_precond) h_precond := by
    have h₄ : (Triple x h_precond) / 3 = x := h₁
    have h₅ : ((Triple x h_precond) / 3) * 3 = Triple x h_precond := h₂
    exact ⟨h₄, by
      simpa [Triple] using h₅⟩

  exact h₃
  -- !benchmark @end proof
