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
def proof_aux (x : Int) (y : Int) : True := by trivial
-- !benchmark @end proof_aux


theorem myMin_spec_satisfied (x: Int) (y: Int) (h_precond : myMin_precond (x) (y)) :
    myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (x ≤ y → myMin x y h_precond = x) ∧ (x > y → myMin x y h_precond = y) := by
    by_cases h : x < y
    · -- Case 1: x < y
      have h₁ : myMin x y h_precond = x := by
        simp [myMin, h]
      constructor
      · -- Prove x ≤ y → myMin x y h_precond = x
        intro h₂
        rw [h₁]
      · -- Prove x > y → myMin x y h_precond = y
        intro h₂
        exfalso
        linarith
    · -- Case 2: ¬(x < y)
      have h₁ : myMin x y h_precond = y := by
        simp [myMin, h]
        <;>
        (try
          {
            by_cases h₂ : x = y
            · simp_all
            · -- If x ≠ y and ¬(x < y), then x > y
              have h₃ : x > y := by
                cases' lt_or_gt_of_ne h₂ with h₂ h₂
                · exfalso
                  linarith
                · exact h₂
              simp_all
          })
        <;>
        (try
          {
            simp_all [lt_irrefl]
          })
        <;>
        (try
          {
            omega
          })
      constructor
      · -- Prove x ≤ y → myMin x y h_precond = x
        intro h₂
        have h₃ : x = y := by
          by_contra h₄
          -- If x ≠ y and ¬(x < y), then x > y
          have h₅ : x > y := by
            cases' lt_or_gt_of_ne h₄ with h₄ h₄
            · exfalso
              linarith
            · exact h₄
          linarith
        rw [h₁, h₃]
      · -- Prove x > y → myMin x y h_precond = y
        intro h₂
        rw [h₁]
  -- Use h_main to prove the main statement
  simp_all [myMin_postcond]
  <;>
  (try
    {
      tauto
    })
  <;>
  (try
    {
      aesop
    })
  <;>
  (try
    {
      simp_all
      <;>
      tauto
    })
  -- !benchmark @end proof
