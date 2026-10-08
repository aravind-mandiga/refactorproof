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
  have h₁ : Triple (x) h_precond = 3 * x := by
    dsimp [Triple]
    <;> ring
    <;> simp [h_precond]
    <;> omega

  have h₂ : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    rw [h₁]
    have h₃ : ((3 * x : ℤ) / 3 = x) := by
      -- Prove that (3 * x) / 3 = x for any integer x
      have h₄ : (3 * x : ℤ) / 3 = x := by
        omega
      exact h₄
    have h₄ : ((3 * x : ℤ) / 3 * 3 = 3 * x) := by
      -- Prove that ((3 * x) / 3) * 3 = 3 * x
      have h₅ : ((3 * x : ℤ) / 3 * 3 = 3 * x) := by
        have h₆ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
          omega
        exact h₆
      exact h₅
    exact ⟨h₃, h₄⟩

  exact h₂
  -- !benchmark @end proof
