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
  let __rp_tmp_6a807069 : Int :=
    if x < y then x else y
  __rp_tmp_6a807069
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
  unfold myMin myMin_postcond
  have h_main_proof : myMin_postcond x y (myMin x y h_precond) h_precond := by
    unfold myMin_postcond
    have h₁ : myMin x y h_precond = if x < y then x else y := by
      rfl
    rw [h₁]
    constructor
    · -- Prove `x ≤ y → (if x < y then x else y) = x`
      intro h
      split_ifs <;>
      (try contradiction) <;>
      (try omega) <;>
      (try simp_all [myMin_precond]) <;>
      (try omega) <;>
      (try
        {
          omega
        }) <;>
      (try
        {
          simp_all [myMin_precond]
          <;> omega
        }) <;>
      (try
        {
          omega
        })
    · -- Prove `x > y → (if x < y then x else y) = y`
      intro h
      have h₂ : ¬ x < y := by
        intro h₃
        have h₄ : x > y := by exact h
        have h₅ : x < y := h₃
        linarith
      split_ifs at * <;> simp_all [myMin_precond]
      <;>
      (try omega) <;>
      (try linarith)
  exact h_main_proof
  -- !benchmark @end proof
