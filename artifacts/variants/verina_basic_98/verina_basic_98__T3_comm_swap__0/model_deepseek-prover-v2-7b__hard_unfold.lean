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
  unfold Triple Triple_postcond
  have h₁ : (Triple x h_precond) / 3 = x := by
    have h₂ : Triple x h_precond = x * 3 := by
      rfl
    rw [h₂]
    -- Now we need to prove that (x * 3) / 3 = x
    -- This is a property of integer division, which is exact here
    have h₃ : (x * 3) / 3 = x := by
      have h₄ : x * 3 / 3 = x := by
        -- Use the fact that x * 3 is divisible by 3
        have h₅ : x * 3 = 3 * x := by ring
        rw [h₅]
        -- Simplify the expression using the property of integer division
        simp [Int.mul_ediv_cancel_left, Int.emod_eq_of_lt] <;> omega
      exact h₄
    exact h₃

  have h₂ : ((Triple x h_precond) / 3) * 3 = Triple x h_precond := by
    have h₃ : (Triple x h_precond) / 3 = x := h₁
    have h₄ : ((Triple x h_precond) / 3) * 3 = Triple x h_precond := by
      rw [h₃]
      <;>
      (try simp [Triple]) <;>
      (try ring) <;>
      (try omega) <;>
      (try simp_all [Triple]) <;>
      (try omega)
    exact h₄

  have h₃ : Triple_postcond (x) (Triple x h_precond) h_precond := by
    constructor
    · -- Prove the first part: (Triple x h_precond) / 3 = x
      simpa [Triple] using h₁
    · -- Prove the second part: ((Triple x h_precond) / 3) * 3 = Triple x h_precond
      simpa [Triple] using h₂
  exact h₃
  -- !benchmark @end proof
