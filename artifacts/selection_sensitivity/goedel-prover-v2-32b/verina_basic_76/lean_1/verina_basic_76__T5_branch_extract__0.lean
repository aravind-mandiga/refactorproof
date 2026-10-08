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
  have h_main : myMin_postcond x y (myMin x y h_precond) h_precond := by
    by_cases h : x < y
    · -- Case: x < y
      have h₁ : myMin x y h_precond = x := by
        simp [myMin, h, h_precond]
      constructor
      · -- Prove x ≤ y → result = x
        intro h₂
        rw [h₁]
        <;> simp_all
      · -- Prove x > y → result = y
        intro h₂
        exfalso
        linarith
    · -- Case: x ≥ y
      have h₁ : myMin x y h_precond = y := by
        simp [myMin, h, h_precond]
        <;>
        (try { contradiction }) <;>
        (try { linarith })
      constructor
      · -- Prove x ≤ y → result = x
        intro h₂
        have h₃ : x = y := by
          have h₄ : x ≥ y := by
            by_contra h₄
            have h₅ : x < y := by linarith
            contradiction
          have h₅ : x ≤ y := h₂
          linarith
        rw [h₁]
        <;> simp [h₃]
      · -- Prove x > y → result = y
        intro h₂
        rw [h₁]
        <;> simp_all
  exact h_main
  -- !benchmark @end proof
