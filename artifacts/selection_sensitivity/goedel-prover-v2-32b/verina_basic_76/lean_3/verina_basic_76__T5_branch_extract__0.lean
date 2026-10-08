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
  have h_main : (x ≤ y → myMin (x) (y) h_precond = x) ∧ (x > y → myMin (x) (y) h_precond = y) := by
    constructor
    · -- Prove x ≤ y → myMin x y = x
      intro hxy
      have h₁ : x < y ∨ x = y := by
        -- Since x ≤ y, either x < y or x = y
        cases' lt_or_eq_of_le hxy with h h
        · exact Or.inl h
        · exact Or.inr h
      cases' h₁ with h₁ h₁
      · -- Case: x < y
        have h₂ : myMin x y h_precond = x := by
          dsimp [myMin]
          simp [h₁]
        exact h₂
      · -- Case: x = y
        have h₂ : myMin x y h_precond = y := by
          dsimp [myMin]
          simp [h₁]
          <;> simp_all [not_lt]
          <;> omega
        have h₃ : myMin x y h_precond = x := by
          rw [h₂]
          <;> linarith
        exact h₃
    · -- Prove x > y → myMin x y = y
      intro hxy
      have h₁ : ¬(x < y) := by
        -- If x > y, then ¬(x < y)
        intro h
        linarith
      have h₂ : myMin x y h_precond = y := by
        dsimp [myMin]
        simp [h₁]
      exact h₂

  dsimp [myMin_postcond] at *
  exact h_main
  -- !benchmark @end proof
