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
  have h_main : myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
    dsimp only [myMin_precond, myMin_postcond, myMin] at *
    split_ifs <;> simp_all [Int.lt_iff_le_and_ne, Int.le_of_lt]
    <;>
    (try { contradiction }) <;>
    (try { omega }) <;>
    (try {
      constructor <;> intro h <;>
      (try { contradiction }) <;>
      (try { omega }) <;>
      (try { linarith })
    })
    <;>
    (try {
      by_cases h : x = y <;> simp_all [h, Int.lt_iff_le_and_ne, Int.le_of_lt]
      <;>
      (try { contradiction }) <;>
      (try { omega }) <;>
      (try { linarith })
    })
    <;>
    (try {
      by_cases h : x < y <;> simp_all [h, Int.lt_iff_le_and_ne, Int.le_of_lt]
      <;>
      (try { contradiction }) <;>
      (try { omega }) <;>
      (try { linarith })
    })
  exact h_main
  -- !benchmark @end proof
