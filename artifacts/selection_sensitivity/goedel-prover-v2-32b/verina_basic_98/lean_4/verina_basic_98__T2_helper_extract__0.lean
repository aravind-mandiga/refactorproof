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

private def Triple__rp_helper_c4a61f58 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  x * 3
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_c4a61f58 x h_precond
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
  have h₁ : (x * 3 : Int) / 3 = x := by
    have h : (x * 3 : Int) / 3 = x := by
      have h₂ : (x * 3 : Int) = 3 * x := by ring
      rw [h₂]
      -- Use the lemma that (n * d) / d = n when d ≠ 0
      have h₃ : (3 : Int) ≠ 0 := by norm_num
      have h₄ : (3 * x : Int) / 3 = x := by
        apply Int.ediv_eq_of_eq_mul_right (by norm_num)
        <;> ring
        <;> norm_num
      exact h₄
    exact h

  have h₂ : ((x * 3 : Int) / 3) * 3 = x * 3 := by
    have h₃ : (x * 3 : Int) / 3 = x := h₁
    rw [h₃]
    <;> ring
    <;> norm_num

  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    dsimp [Triple, Triple_postcond] at *
    -- Now we need to prove that (x * 3) / 3 = x and ((x * 3) / 3) * 3 = x * 3
    constructor
    · -- Prove (x * 3) / 3 = x
      exact h₁
    · -- Prove ((x * 3) / 3) * 3 = x * 3
      exact h₂

  exact h_main
  -- !benchmark @end proof
