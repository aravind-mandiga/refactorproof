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
  have h_main : (x ≤ y → myMin (x) (y) h_precond = x) ∧ (x > y → myMin (x) (y) h_precond = y) := by
    constructor
    · -- Prove x ≤ y → myMin x y h_precond = x
      intro hxy
      -- Since x ≤ y, we consider two cases: x < y or x = y
      by_cases h : x < y
      · -- Case x < y
        simp_all [myMin, h_precond]
        <;> omega
      · -- Case x ≥ y
        have h' : x ≥ y := by omega
        have h'' : x = y := by
          -- Since x ≥ y and x < y is false, we have x = y
          by_contra hxy'
          have h1 : x > y := by
            cases' lt_or_gt_of_ne hxy' with h1 h1 <;> omega
          omega
        simp_all [myMin, h_precond]
        <;> omega
    · -- Prove x > y → myMin x y h_precond = y
      intro hxy
      -- Since x > y, we have ¬(x ≤ y) and x ≠ y
      have h₁ : ¬x ≤ y := by
        intro h₂
        have h₃ : x > y := by assumption
        linarith
      have h₂ : ¬(x < y) := by
        intro h₂
        have h₃ : x ≤ y := by
          by_cases h₄ : x = y
          · linarith
          · omega
        contradiction
      -- Simplify the expression for myMin using the above facts
      simp_all [myMin, h_precond, not_lt]
      <;> (try omega) <;> (try simp_all [Int.lt_iff_add_one_le]) <;> (try omega)
  -- Extract the two implications from h_main and use them to prove the postcondition
  exact ⟨h_main.1, h_main.2⟩
  -- !benchmark @end proof
