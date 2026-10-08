-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def myMin__rp_helper_829c4a21 (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  if a <= b then a else b
-- !benchmark @end code_aux


def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  -- !benchmark @start code
  myMin__rp_helper_829c4a21 a b h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def myMin_postcond (a : Int) (b : Int) (result: Int) (h_precond : myMin_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem myMin_spec_satisfied (a: Int) (b: Int) (h_precond : myMin_precond (a) (b)) :
    myMin_postcond (a) (b) (myMin (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : myMin_postcond (a) (b) (myMin (a) (b) h_precond) h_precond := by
    have h₁ : myMin (a) (b) h_precond ≤ a ∧ myMin (a) (b) h_precond ≤ b := by
      by_cases h : a ≤ b
      · -- Case: a ≤ b
        have h₂ : myMin (a) (b) h_precond = a := by
          simp [myMin, h]
          <;> aesop
        rw [h₂]
        constructor
        · -- Prove a ≤ a
          linarith
        · -- Prove a ≤ b
          linarith
      · -- Case: a > b
        have h₂ : myMin (a) (b) h_precond = b := by
          simp [myMin, h]
          <;> aesop
        rw [h₂]
        constructor
        · -- Prove b ≤ a
          have h₃ : b ≤ a := by
            linarith
          linarith
        · -- Prove b ≤ b
          linarith
    have h₂ : (myMin (a) (b) h_precond = a ∨ myMin (a) (b) h_precond = b) := by
      by_cases h : a ≤ b
      · -- Case: a ≤ b
        have h₃ : myMin (a) (b) h_precond = a := by
          simp [myMin, h]
          <;> aesop
        exact Or.inl h₃
      · -- Case: a > b
        have h₃ : myMin (a) (b) h_precond = b := by
          simp [myMin, h]
          <;> aesop
        exact Or.inr h₃
    exact ⟨h₁, h₂⟩
  exact h_main
  -- !benchmark @end proof
