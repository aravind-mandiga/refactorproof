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

-- !benchmark @end code_aux


def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  -- !benchmark @start code
  let __rp_tmp_bc3c77e2 : Int :=
    if a <= b then a else b
  __rp_tmp_bc3c77e2
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
    have h₁ : (myMin (a) (b) h_precond ≤ a ∧ myMin (a) (b) h_precond ≤ b) ∧ (myMin (a) (b) h_precond = a ∨ myMin (a) (b) h_precond = b) := by
      by_cases h : a ≤ b
      · -- Case: a ≤ b
        have h₂ : myMin (a) (b) h_precond = a := by
          rw [myMin]
          simp [h]
        rw [h₂]
        constructor
        · -- Prove a ≤ a ∧ a ≤ b
          constructor
          · -- Prove a ≤ a
            linarith
          · -- Prove a ≤ b
            linarith
        · -- Prove a = a ∨ a = b
          exact Or.inl rfl
      · -- Case: ¬ (a ≤ b) which implies b < a
        have h₂ : myMin (a) (b) h_precond = b := by
          rw [myMin]
          simp [h]
          <;>
          (try omega) <;>
          (try linarith)
        rw [h₂]
        constructor
        · -- Prove b ≤ a ∧ b ≤ b
          constructor
          · -- Prove b ≤ a
            have h₃ : b < a := by
              by_contra h₄
              have h₅ : a ≤ b := by linarith
              contradiction
            linarith
          · -- Prove b ≤ b
            linarith
        · -- Prove b = a ∨ b = b
          exact Or.inr rfl
    exact h₁
  exact h_main
  -- !benchmark @end proof
