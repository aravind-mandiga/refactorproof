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

-- !benchmark @end code_aux


def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  -- !benchmark @start code
  let __rp_tmp_6a807069 : Int :=
    if x < y then x else y
  __rp_tmp_6a807069
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
  unfold myMin myMin_postcond
  have h_main : myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
    constructor
    · -- Prove the first part: x ≤ y → myMin x y = x
      intro h
      have h₁ : x ≤ y := h
      -- Consider the cases for x and y
      by_cases h₂ : x < y
      · -- Case 1: x < y
        have h₃ : myMin (x) (y) h_precond = x := by
          simp [myMin, h₂]
          <;> omega
        simp [h₃]
        <;> omega
      · -- Case 2: x ≥ y
        have h₃ : x ≥ y := by omega
        have h₄ : myMin (x) (y) h_precond = y := by
          simp [myMin, h₂, h₃]
          <;> omega
        have h₅ : x ≤ y := by omega
        simp [h₄, h₅]
        <;> omega
    · -- Prove the second part: x > y → myMin x y = y
      intro h
      have h₁ : x > y := h
      -- Consider the cases for x and y
      by_cases h₂ : x < y
      · -- This case is impossible since x > y and x < y cannot both be true
        exfalso
        omega
      · -- Case 1: x ≥ y
        have h₃ : x ≥ y := by omega
        have h₄ : myMin (x) (y) h_precond = y := by
          simp [myMin, h₂, h₃]
          <;> omega
        simp [h₄]
        <;> omega
  exact h_main
  -- !benchmark @end proof
