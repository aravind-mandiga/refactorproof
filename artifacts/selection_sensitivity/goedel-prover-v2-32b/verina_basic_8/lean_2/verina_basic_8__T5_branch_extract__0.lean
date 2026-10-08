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

private def myMin__rp_branch_c77e3e9a (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  b
-- !benchmark @end code_aux


def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  -- !benchmark @start code
  if a <= b then a else
    myMin__rp_branch_c77e3e9a a b h_precond
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
  have h_main : myMin_postcond a b (myMin a b h_precond) h_precond := by
    dsimp [myMin_postcond, myMin, myMin_precond] at *
    split_ifs with h
    · -- Case: a ≤ b
      constructor
      · -- Prove result ≤ a ∧ result ≤ b
        constructor
        · -- Prove a ≤ a
          linarith
        · -- Prove a ≤ b
          linarith
      · -- Prove result = a ∨ result = b
        exact Or.inl rfl
    · -- Case: ¬(a ≤ b)
      constructor
      · -- Prove result ≤ a ∧ result ≤ b
        constructor
        · -- Prove b ≤ a
          -- Since ¬(a ≤ b), we have a > b, so b < a, hence b ≤ a
          have h₁ : a > b := by
            by_contra h₁
            -- If a ≤ b, then we have a contradiction with h : ¬(a ≤ b)
            have h₂ : a ≤ b := by linarith
            contradiction
          linarith
        · -- Prove b ≤ b
          linarith
      · -- Prove result = a ∨ result = b
        exact Or.inr rfl
  exact h_main
  -- !benchmark @end proof
