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
  have h₁ : Triple (x) h_precond = 3 * x := by
    dsimp [Triple]
    <;> ring
    <;> norm_num
    <;> omega

  have h₂ : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    rw [h₁]
    constructor
    · -- Prove (3 * x) / 3 = x
      have h₃ : (3 * x : ℤ) / 3 = x := by
        -- Prove that (3 * x) / 3 = x using the fact that 3 * x is a multiple of 3
        omega
      exact h₃
    · -- Prove (3 * x) / 3 * 3 = 3 * x
      have h₃ : ((3 * x : ℤ) / 3 * 3) = 3 * x := by
        -- Prove that ((3 * x) / 3 * 3) = 3 * x
        omega
      exact h₃

  exact h₂
  -- !benchmark @end proof
