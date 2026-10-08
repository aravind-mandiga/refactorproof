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
    have h₁ : myMin (a) (b) h_precond ≤ a ∧ myMin (a) (b) h_precond ≤ b ∧ (myMin (a) (b) h_precond = a ∨ myMin (a) (b) h_precond = b) := by
      constructor
      · -- Prove that `myMin (a) (b) h_precond ≤ a`
        have h₂ : myMin (a) (b) h_precond = if a ≤ b then a else b := rfl
        rw [h₂]
        split_ifs <;>
        (try { contradiction }) <;>
        (try { linarith }) <;>
        (try { simp_all }) <;>
        (try { omega }) <;>
        (try { exact le_rfl })
        <;>
        (try { exact le_of_lt (by omega) })
        <;>
        (try { linarith })
      · constructor
        · -- Prove that `myMin (a) (b) h_precond ≤ b`
          have h₃ : myMin (a) (b) h_precond = if a ≤ b then a else b := rfl
          rw [h₃]
          split_ifs <;>
          (try { contradiction }) <;>
          (try { linarith }) <;>
          (try { simp_all }) <;>
          (try { omega }) <;>
          (try { exact le_rfl })
          <;>
          (try { exact le_of_lt (by omega) })
          <;>
          (try { linarith })
        · -- Prove that `myMin (a) (b) h_precond = a ∨ myMin (a) (b) h_precond = b`
          have h₄ : myMin (a) (b) h_precond = if a ≤ b then a else b := rfl
          rw [h₄]
          split_ifs <;>
          (try { contradiction }) <;>
          (try { aesop }) <;>
          (try { omega }) <;>
          (try { exact Or.inl rfl }) <;>
          (try { exact Or.inr rfl })
          <;>
          (try { aesop })
    simp_all [myMin_postcond, myMin_precond]
    <;> aesop
  exact h_main
  -- !benchmark @end proof
