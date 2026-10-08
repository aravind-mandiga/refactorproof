-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def myMin_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def myMin__rp_branch_b558f2ed (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  y
-- !benchmark @end code_aux


def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  -- !benchmark @start code
  if x < y then x else
    myMin__rp_branch_b558f2ed x y h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  -- !benchmark @start postcond
  (x ≤ y → result = x) ∧ (x > y → result = y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem myMin_spec_satisfied (x: Int) (y: Int) (h_precond : myMin_precond (x) (y)) :
    myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : x ≤ y → myMin x y h_precond = x := by
    intro h_le
    have h₂ : myMin x y h_precond = x := by
      -- Prove that if x ≤ y, then myMin x y = x
      by_cases h : x < y
      · -- Case: x < y
        simp [myMin, h]
      · -- Case: x ≥ y
        have h₃ : y ≤ x := by
          by_contra h₄
          have h₅ : x < y := by
            linarith
          contradiction
        have h₄ : x = y := by
          have h₅ : x ≤ y := h_le
          have h₆ : y ≤ x := h₃
          linarith
        simp [myMin, h, h₄]
        <;> aesop
    exact h₂
    <;> aesop

  have h₂ : x > y → myMin x y h_precond = y := by
    intro h_gt
    have h₃ : ¬(x < y) := by
      intro h_lt
      have h₄ : x ≤ y := by
        linarith
      have h₅ : x > y := h_gt
      linarith
    have h₄ : myMin x y h_precond = y := by
      simp [myMin, h₃]
    exact h₄

  have h_main : myMin_postcond x y (myMin x y h_precond) h_precond := by
    constructor
    · -- Prove the first part: x ≤ y → myMin x y h_precond = x
      intro h_le
      exact h₁ h_le
    · -- Prove the second part: x > y → myMin x y h_precond = y
      intro h_gt
      exact h₂ h_gt

  exact h_main
  -- !benchmark @end proof
