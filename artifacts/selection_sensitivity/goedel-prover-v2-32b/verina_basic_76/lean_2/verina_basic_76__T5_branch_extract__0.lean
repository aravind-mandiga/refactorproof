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
  have h_main : (x ≤ y → (if x < y then x else y) = x) ∧ (x > y → (if x < y then x else y) = y) := by
    constructor
    · -- Prove the first part: x ≤ y → (if x < y then x else y) = x
      intro h_le
      split_ifs <;>
      (try { contradiction }) <;>
      (try { linarith }) <;>
      (try { simp_all }) <;>
      (try { omega }) <;>
      (try { linarith })
    · -- Prove the second part: x > y → (if x < y then x else y) = y
      intro h_gt
      split_ifs <;>
      (try { contradiction }) <;>
      (try { linarith }) <;>
      (try { simp_all }) <;>
      (try { omega }) <;>
      (try { linarith })

  -- Simplify the goal using the definition of myMin and myMin_postcond
  simp only [myMin, myMin_postcond] at h_main ⊢

  -- Use the results from h_main to complete the proof
  tauto
  -- !benchmark @end proof
