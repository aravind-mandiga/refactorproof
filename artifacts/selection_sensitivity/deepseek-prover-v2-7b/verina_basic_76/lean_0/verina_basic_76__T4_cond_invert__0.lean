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
  if ¬ (x < y) then y
  else x
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
  have h_main : myMin_postcond x y (myMin x y h_precond) h_precond := by
    unfold myMin_postcond
    constructor
    · -- Prove x ≤ y → myMin x y h_precond = x
      intro h
      have h₁ : (if x < y then x else y) = x := by
        split_ifs <;> simp_all [myMin, myMin_precond] <;> omega
      simp_all [myMin]
      <;> aesop
    · -- Prove x > y → myMin x y h_precond = y
      intro h
      have h₁ : (if x < y then x else y) = y := by
        split_ifs <;> simp_all [myMin, myMin_precond] <;> try omega
        <;> try linarith
      simp_all [myMin]
      <;> aesop
  exact h_main
  -- !benchmark @end proof
