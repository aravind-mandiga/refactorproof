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

private def myMin__rp_helper_5e5dcb4d (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  if x < y then x else y
-- !benchmark @end code_aux


def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  -- !benchmark @start code
  myMin__rp_helper_5e5dcb4d x y h_precond
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
  have h_main : (x ≤ y → (if x < y then x else y) = x) ∧ (x > y → (if x < y then x else y) = y) := by
    constructor
    · -- Prove x ≤ y → (if x < y then x else y) = x
      intro h_xy
      split_ifs with h_lt
      · -- Case x < y
        -- Since x < y, the if condition is true, and we need to show x = x
        rfl
      · -- Case ¬(x < y)
        -- Here, x ≥ y. But we have x ≤ y, so x = y
        have h_eq : x = y := by
          have h₁ : x ≥ y := by
            -- Since ¬(x < y), we have x ≥ y
            omega
          -- Given x ≤ y and x ≥ y, we have x = y
          omega
        -- Substitute x = y into the else branch
        rw [h_eq]
        <;> simp_all
        <;> omega
    · -- Prove x > y → (if x < y then x else y) = y
      intro h_xy
      split_ifs with h_lt
      · -- Case x < y
        -- This case is impossible because x > y
        exfalso
        omega
      · -- Case ¬(x < y)
        -- The else branch directly gives y
        rfl

  have h_final : myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
    simp only [myMin_postcond, myMin] at *
    -- Use the result from h_main to directly conclude the proof
    have h₁ : (x ≤ y → (if x < y then x else y) = x) := h_main.1
    have h₂ : (x > y → (if x < y then x else y) = y) := h_main.2
    constructor
    · -- Prove x ≤ y → (if x < y then x else y) = x
      intro h
      have h₃ := h₁ h
      simpa using h₃
    · -- Prove x > y → (if x < y then x else y) = y
      intro h
      have h₃ := h₂ h
      simpa using h₃

  exact h_final
  -- !benchmark @end proof
