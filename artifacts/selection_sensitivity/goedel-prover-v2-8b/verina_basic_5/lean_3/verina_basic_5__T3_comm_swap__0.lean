-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  -- !benchmark @start code
  b * a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  -- !benchmark @start postcond
  result - a * b = 0 ∧ a * b - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem multiply_spec_satisfied (a: Int) (b: Int) (h_precond : multiply_precond (a) (b)) :
    multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (multiply (a) (b) h_precond) - a * b = 0 ∧ a * b - (multiply (a) (b) h_precond) = 0 := by
    have h₁ : multiply (a) (b) h_precond = a * b := by
      simp [multiply]
      <;> aesop
    constructor
    · -- Prove (multiply (a) (b) h_precond) - a * b = 0
      rw [h₁]
      <;> ring
      <;> simp
    · -- Prove a * b - (multiply (a) (b) h_precond) = 0
      rw [h₁]
      <;> ring
      <;> simp
  exact h_main
  -- !benchmark @end proof
