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

private def lastDigit__rp_helper_8d571788 (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  n % 10
-- !benchmark @end code_aux


def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  -- !benchmark @start code
  lastDigit__rp_helper_8d571788 n h_precond
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
  unfold lastDigit lastDigit_postcond
  have h₁ : lastDigit (n) h_precond = n % 10 := by
    simp [lastDigit]
    <;> aesop

  have h₂ : 0 ≤ n % 10 ∧ n % 10 < 10 := by
    have h₂ : n % 10 < 10 := Nat.mod_lt _ (by decide)
    have h₃ : 0 ≤ n % 10 := Nat.zero_le _
    exact ⟨h₃, h₂⟩

  have h₃ : n % 10 - (n % 10) = 0 := by
    have h₃ : n % 10 ≥ 0 := by omega
    have h₄ : n % 10 - (n % 10) = 0 := by
      apply Nat.sub_self
    exact h₄

  have h₄ : (n % 10) - (n % 10) = 0 := by
    have h₄ : n % 10 - (n % 10) = 0 := by
      apply Nat.sub_self
    exact h₄

  have h₅ : lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
    rw [h₁]
    have h₅₁ : 0 ≤ (n % 10 : ℕ) ∧ (n % 10 : ℕ) < 10 := by simpa using h₂
    have h₅₂ : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := by simpa using h₄
    have h₅₃ : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := by simpa using h₃
    simp_all [lastDigit_postcond, lastDigit_precond]
    <;> omega

  apply h₅
  -- !benchmark @end proof
