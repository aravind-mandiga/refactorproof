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
  have h_main₁ : x ≤ y → myMin (x) (y) h_precond = x := by
    intro h_le
    have h₁ : x < y ∨ x = y := by
      by_cases h : x < y
      · exact Or.inl h
      · have h₂ : x ≥ y := by
          omega
        have h₃ : x = y := by
          omega
        exact Or.inr h₃
    cases h₁ with
    | inl h_lt =>
      have h₂ : myMin (x) (y) h_precond = x := by
        rw [myMin]
        simp [h_lt]
      exact h₂
    | inr h_eq =>
      have h₂ : myMin (x) (y) h_precond = y := by
        rw [myMin]
        simp [h_eq]
      have h₃ : y = x := by
        linarith
      rw [h₂, h₃]
      <;> simp_all

  have h_main₂ : x > y → myMin (x) (y) h_precond = y := by
    intro h_gt
    have h₁ : ¬x < y := by
      intro h_lt
      linarith
    have h₂ : myMin (x) (y) h_precond = y := by
      rw [myMin]
      split_ifs at * <;> simp_all [Int.lt_irrefl]
      <;> omega
    exact h₂

  constructor
  · -- Prove the first part of the conjunction: x ≤ y → result = x
    intro h_le
    have h₃ : myMin (x) (y) h_precond = x := h_main₁ h_le
    simpa using h₃
  · -- Prove the second part of the conjunction: x > y → result = y
    intro h_gt
    have h₃ : myMin (x) (y) h_precond = y := h_main₂ h_gt
    simpa using h₃
  -- !benchmark @end proof
