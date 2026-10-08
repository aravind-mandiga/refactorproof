-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_c1b8a8ca : Nat :=
    n % 10
  __rp_tmp_c1b8a8ca
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  -- !benchmark @start postcond
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lastDigit_spec_satisfied (n: Nat) (h_precond : lastDigit_precond (n)) :
    lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : lastDigit n h_precond = n % 10 := by
    simp [lastDigit]
    <;>
    trivial

  have h₂ : 0 ≤ lastDigit n h_precond ∧ lastDigit n h_precond < 10 := by
    have h₂₁ : lastDigit n h_precond = n % 10 := h₁
    have h₂₂ : 0 ≤ n % 10 := by
      exact Nat.zero_le _
    have h₂₃ : n % 10 < 10 := by
      exact Nat.mod_lt _ (by norm_num)
    constructor
    · -- Prove 0 ≤ lastDigit n h_precond
      rw [h₂₁]
      <;> exact h₂₂
    · -- Prove lastDigit n h_precond < 10
      rw [h₂₁]
      <;> exact h₂₃

  have h₃ : n % 10 - lastDigit n h_precond = 0 := by
    have h₃₁ : lastDigit n h_precond = n % 10 := h₁
    rw [h₃₁]
    <;>
    simp [Nat.sub_self]
    <;>
    omega

  have h₄ : lastDigit n h_precond - n % 10 = 0 := by
    have h₄₁ : lastDigit n h_precond = n % 10 := h₁
    rw [h₄₁]
    <;>
    simp [Nat.sub_self]
    <;>
    omega

  have h₅ : lastDigit_postcond n (lastDigit n h_precond) h_precond := by
    have h₅₁ : (0 ≤ lastDigit n h_precond ∧ lastDigit n h_precond < 10) := h₂
    have h₅₂ : n % 10 - lastDigit n h_precond = 0 := h₃
    have h₅₃ : lastDigit n h_precond - n % 10 = 0 := h₄
    simp only [lastDigit_postcond] at *
    constructor
    · -- Prove 0 ≤ result ∧ result < 10
      exact h₅₁
    · -- Prove n % 10 - result = 0 ∧ result - n % 10 = 0
      constructor
      · -- Prove n % 10 - result = 0
        exact h₅₂
      · -- Prove result - n % 10 = 0
        exact h₅₃
  exact h₅
  -- !benchmark @end proof
