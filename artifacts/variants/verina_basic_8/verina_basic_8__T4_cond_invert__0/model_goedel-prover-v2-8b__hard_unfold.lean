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
  if ¬ (a <= b) then b
  else a
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
  unfold myMin myMin_postcond
  have h_main : myMin_postcond (a) (b) (myMin (a) (b) h_precond) h_precond := by
    simp only [myMin_postcond, myMin_precond, myMin, h_precond, True] at *
    -- Simplify the goal using the definitions and the fact that h_precond is trivially true
    by_cases h : a ≤ b
    · -- Case: a ≤ b
      simp [h, le_of_lt, le_of_lt, le_of_lt]
      <;>
      (try omega) <;>
      (try
        {
          norm_num
          <;>
          omega
        }) <;>
      (try
        {
          aesop
        })
    · -- Case: a > b
      have h' : b ≤ a := by
        linarith
      simp [h, h', le_of_lt, le_of_lt, le_of_lt]
      <;>
      (try omega) <;>
      (try
        {
          norm_num
          <;>
          omega
        }) <;>
      (try
        {
          aesop
        })
  exact h_main
  -- !benchmark @end proof
